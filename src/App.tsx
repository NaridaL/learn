import React, {
	Component,
	ReactNode,
	MouseEvent,
	TouchEvent,
	PureComponent,
	Props,
	HTMLAttributes,
} from "react"
import querystring from "querystring"
import { int, V3, V, M4, DEG } from "ts3dutils"
import slugify from "slugify"
import { CardText, Button, Alert, Input, ButtonGroup } from "reactstrap"
import { Converter } from "showdown"
import _ from "lodash-es"
import { Gists, GistDescriptor } from "./gists"

import ReactDOM from "react-dom"
import {
	Link,
	Switch,
	Route,
	Redirect,
	RouteComponentProps,
} from "react-router-dom"
import Container from "reactstrap/lib/Container"
import FormGroup from "reactstrap/lib/FormGroup"

import graphsMarkdown from "../content/graphs.md"
import optalgoMarkdown from "../content/optalgo.md"
import robMarkdown from "../content/rob.md"

const cardMarkdowns = {
	graphs: graphsMarkdown,
	optalgo: optalgoMarkdown,
	rob: robMarkdown,
}

const converter = new Converter({ literalMidWordUnderscores: true })
type CardStates = { [slug: string]: CardState }
const gs = new Gists(localStorage.getItem("learn_gisthub_token"))
let saveGist: GistDescriptor
function getCardState(states: CardStates, slug: string) {
	return (
		states[slug] || {
			level: 1,
			correct: [],
			incorrect: [],
		}
	)
}

async function initSaving(): Promise<GistDescriptor> {
	const gists = await gs.all()
	const saveGistInfo = gists.find(gist => gist.description === "learn saves")
	if (!saveGistInfo) {
		console.log("Creating new gist")

		saveGist = await gs.createGist(
			{ graphs: { content: "{}" } },
			"learn saves",
			false,
		)
	} else {
		console.log("Found existing matching gist " + saveGistInfo.id)

		saveGist = await gs.getGist(saveGistInfo.id)
	}
	return saveGist
}
const saveGistPromise = initSaving()

interface GitHubFile {
	type: "file"
	encoding: "base64"
	size: number
	name: string
	path: string
	content: string
	sha: string
	url: string // eg "https://api.github.com/repos/octokit/octokit.rb/contents/README.md"
	git_url: string // eg "https://api.github.com/repos/octokit/octokit.rb/git/blobs/3d21ec53a331a6f037a91c368710b99387d012c1"
	html_url: string // eg "https://github.com/octokit/octokit.rb/blob/master/README.md"
	download_url: string // eg "https://raw.githubusercontent.com/octokit/octokit.rb/master/README.md"
	_links: {
		git: string // eg "https://api.github.com/repos/octokit/octokit.rb/git/blobs/3d21ec53a331a6f037a91c368710b99387d012c1"
		self: string // eg "https://api.github.com/repos/octokit/octokit.rb/contents/README.md"
		html: string // eg "https://github.com/octokit/octokit.rb/blob/master/README.md"
	}
}
function b64EncodeUnicode(str) {
	// first we use encodeURIComponent to get percent-encoded UTF-8,
	// then we convert the percent encodings into raw bytes which
	// can be fed into btoa.
	return btoa(
		encodeURIComponent(str).replace(
			/%([0-9A-F]{2})/g,
			function toSolidBytes(match, p1) {
				return String.fromCharCode(parseInt(p1, 16))
			},
		),
	)
}

function b64DecodeUnicode(str) {
	// Going backwards: from bytestream, to percent-encoding, to original string.
	return decodeURIComponent(
		atob(str)
			.split("")
			.map(function(c) {
				return "%" + ("00" + c.charCodeAt(0).toString(16)).slice(-2)
			})
			.join(""),
	)
}

function updateCard(subject: string, card: Card, newText: string) {
	const path = "content/" + subject + ".md"
	const contentURL =
		"https://api.github.com/repos/" +
		"NaridaL" +
		"/" +
		"learn" +
		"/contents/" +
		encodeURI(path) +
		"?" +
		querystring.stringify({ access_token: gs.token, ref: "master" })
	return fetch(contentURL, {
		cache: "no-store",
	})
		.then(r => r.json() as Promise<GitHubFile>)
		.then(({ sha, content }) => {
			const newCards = parseCards(b64DecodeUnicode(content)).map(
				c =>
					c.slug == card.slug
						? {
								title: card.title,
								slug: card.slug,
								content: newText,
						  }
						: c,
			)
			const newContentContent = newCards
				.map(
					c =>
						"# " +
						c.title.trim() +
						"\n\n" +
						c.content.trim() +
						"\n",
				)
				.join("\n")
			console.log("new content" + newContentContent)
			return Promise.all([
				fetch(contentURL + "?", {
					method: "PUT",
					body: JSON.stringify({
						message: "update card " + card.title,
						content: b64EncodeUnicode(newContentContent),
						sha,
					}),
				}),
			])
		})
		.then(([newCards, r]) => newCards)
}
function getCardsFromGitHub(subject: string) {
	return fetch("content/" + subject + ".md", {
		cache: "no-store",
	})
		.then(r => r.text())
		.then(content => parseCards(content))
}

class Card {
	constructor(
		public readonly title: string,
		public readonly slug: string,
		public readonly content: string,
	) {}
}

function parseCards(contentMarkdown: string): Card[] {
	const cardRegex = /^#(.*)$\s*(?:^slug:(.*)$)?([\s\S]*)/m
	const cardTexts = contentMarkdown
		.split(/^(?=#[^#])/gm)
		.map(x => x.trim())
		.filter(x => x !== "")
	return cardTexts.map(text => {
		const [, title, slug, content] = text.match(cardRegex)
		return new Card(
			title.trim(),
			slug ? slug.trim() : slugify(title),
			content.trim(),
		)
	})
}
interface CardState {
	level: int
	correct: Date[]
	incorrect: Date[]
}
class SubjectState {
	cards: Card[] = []
	cardStates: CardStates = {}
	queue: Card[] = []
	viewFront = true
	redirect?: string
	info?: string
	error?: string
}
function reviveJSONSave(json: {
	[x: string]: { incorrect: string[]; correct: string[] }
}) {
	console.log(json)
	const result = {}
	Object.keys(json).forEach(slug => {
		const { correct, incorrect } = json[slug]
		result[slug] = {
			correct: correct.map(x => new Date(x)),
			incorrect: incorrect.map(x => new Date(x)),
		}
		fixLevel(result[slug])
	})
	return result
}
function fixLevel(x: CardState) {
	if (x.incorrect.length == 0) {
		x.level = 1 + x.correct.length
	} else {
		x.level =
			1 +
			x.correct
				.slice(x.correct.length - 4)
				.filter(y => y > x.incorrect.last).length
	}
}
function mergeSaves(a: CardStates, b: CardStates) {
	function merge(c: CardState, d: CardState) {
		c.correct = _.unionBy(c.correct, d.correct, x => x.getTime()).sort(
			(a, b) => a.valueOf() - b.valueOf(),
		)
		c.incorrect = _.unionBy(c.incorrect, d.incorrect, x =>
			x.getTime(),
		).sort((a, b) => a.valueOf() - b.valueOf())
		fixLevel(c)
	}
	Object.keys(b).forEach(slug => {
		if (!a[slug]) {
			a[slug] = b[slug]
		} else {
			merge(a[slug], b[slug])
		}
	})
}

export function SubjectOverview(props: RouteComponentProps) {
	return (
		<ul>
			{Object.keys(cardMarkdowns).map(subject => (
				<li>
					<Link to={"/" + subject}>{subject}</Link>
				</li>
			))}
		</ul>
	)
}
export function App() {
	return (
		<Container style={{ height: "100%" }}>
			<Route exact path="/" component={SubjectOverview} />
			<Route path="/:subject" component={Subject} />
		</Container>
	)
}

export class Subject extends Component<
	RouteComponentProps<{ subject: string }>,
	SubjectState
> {
	public state = new SubjectState()

	constructor(props: RouteComponentProps<{ subject: string }>) {
		super(props)
		this.updateCards()
	}

	updateCards() {
		const subject = this.props.match.params.subject
		this.setState({
			cards: parseCards(cardMarkdowns[subject]),
			cardStates: localStorage.getItem("save_graphs")
				? reviveJSONSave(
						JSON.parse(localStorage.getItem("save_graphs")),
				  )
				: {},
		})
		getCardsFromGitHub(subject).then(cards => this.setState({ cards }))
		if (localStorage.getItem("learn_gisthub_token")) {
			saveGistPromise
				.then(gist => {
					console.log("loaded levels from gist")
					this.setState(({ cardStates }) => {
						mergeSaves(
							cardStates,
							reviveJSONSave(
								gist.files[subject]
									? JSON.parse(gist.files[subject].content)
									: {},
							),
						)
						console.log(cardStates)
						return { cardStates }
					})
				})
				.catch(console.error)
		}
	}
	componentDidUpdate(prevProps) {
		// Typical usage (don't forget to compare props):
		if (
			this.props.match.params.subject !== prevProps.match.params.subject
		) {
			this.updateCards()
		}
		console.log("Running mathjax")
		MathJax.Hub.Queue(["Typeset", MathJax.Hub, ReactDOM.findDOMNode(this)])
	}

	public render() {
		if (this.state.redirect) {
			const result = <Redirect push to={this.state.redirect} />
			this.state.redirect = undefined
			return result
		}
		const subject = this.props.match.params.subject
		const { cards } = this.state
		return (
			<>
				<Route
					path="/:subject/card/:cardslug"
					render={match => [
						<BackToOverview subject={subject} />,
						<CardCard
							subject={subject}
							card={cards.find(
								c => c.slug == match.match.params.cardslug,
							)}
						/>,
					]}
				/>
				<Route
					exact
					path="/:subject/learn/:level"
					render={({ match }) => {
						console.log(
							cards.filter(
								c =>
									getCardState(this.state.cardStates, c.slug)
										.level === +match.params.level,
							),
						)
						const levelCards = cards.filter(
							c =>
								getCardState(this.state.cardStates, c.slug)
									.level === +match.params.level,
						)
						if (0 == levelCards.length) {
							this.state.info =
								"No more cards in level " + match.params.level
							return <Redirect to={"/" + subject} />
						}
						const testCard = _.sample(levelCards)
						return (
							<CardQuestion
								card={testCard}
								subject={subject}
								onContinue={() =>
									this.setState({
										redirect:
											"/" +
											subject +
											"/learn/" +
											match.params.level +
											"/answer/" +
											testCard.slug,
									})
								}
							/>
						)
					}}
				/>
				<Route
					exact
					path="/:subject/learn/:level/answer/:cardslug"
					render={({ match }) => {
						const card = cards.find(
							c => c.slug == match.params.cardslug,
						)
						return (
							<CardAnswer
								card={card}
								subject={subject}
								answer={correct =>
									this.answer(correct, card, match)
								}
							/>
						)
					}}
				/>
				<Route
					exact
					path="/:subject/"
					render={match => {
						const result = (
							<CardOverview
								cards={cards}
								subject={subject}
								cardStates={this.state.cardStates}
								info={this.state.info}
								error={this.state.error}
							/>
						)
						this.state.info = undefined
						return result
					}}
				/>
				<Route
					exact
					path="/:subject/edit/:cardslug"
					component={EditCard}
				/>
				<Route path="*" render={match => JSON.stringify(match)} />
			</>
		)
	}

	answer = (correct: boolean, card: Card, match: any) => {
		console.log("answering")
		const subject = this.props.match.params.subject
		const currentCardState = getCardState(this.state.cardStates, card.slug)
		const newLevel = correct ? currentCardState.level + 1 : 1
		const newCorrect = correct
			? [...currentCardState.correct, new Date()]
			: currentCardState.correct
		const newIncorrect = correct
			? currentCardState.incorrect
			: [...currentCardState.incorrect, new Date()]
		const newCardStates = {
			...this.state.cardStates,
			[card.slug]: {
				level: newLevel,
				correct: newCorrect,
				incorrect: newIncorrect,
			},
		}
		this.saveLevels(newCardStates)
		this.setState({
			cardStates: newCardStates,
			redirect: "/" + subject + "/learn/" + match.params.level,
		})
	}
	saverController: AbortController
	saveLevels = (newLevels: CardStates): void => {
		// this.saverController && this.saverController.abort()
		this.saverController = new AbortController()
		const saveJSON = JSON.stringify(
			newLevels,
			(key: string, value: any) => {
				if (value instanceof Date) return value.toISOString()

				if ("level" == key) return undefined
				return value
			},
			"\t",
		)
		localStorage.setItem("save_graphs", saveJSON)
		gs.editGist(
			saveGist.id,
			{
				graphs: {
					content: saveJSON,
				},
			},
			{ signal: this.saverController.signal },
		)
			.then(() => console.log("saved levels"))
			.catch(err => {
				console.log("error?")
				this.setState({ error: err })
				console.error(err)
			})
	}
}

export function CardCard(
	props: { card: Card; subject: string } & HTMLAttributes<HTMLDivElement>,
) {
	const { card, style, subject, ...htmlAttributes } = props
	if (!card) {
		return <div>card undefined</div>
	}
	console.log("rederning cardcard")
	return (
		<div {...htmlAttributes} style={{ ...style, padding: "4px" }}>
			<h3 style={{ textAlign: "center" }}>{card.title}</h3>
			<Link to={"/" + subject + "/edit/" + card.slug}>Edit</Link>
			<div
				dangerouslySetInnerHTML={{
					__html: converter.makeHtml(card.content),
				}}
			/>
		</div>
	)
}

export function CardAnswer({
	card,
	answer,
	subject,
}: {
	subject: string
	card: Card
	answer: (x: boolean) => void
}) {
	return (
		<div
			style={{
				display: "flex",
				flexDirection: "column",
				height: "100%",
			}}
		>
			<BackToOverview subject={subject} />
			<CardCard subject={subject} card={card} style={{ flexGrow: 1 }} />
			<div>
				<Button
					style={{ width: "50%" }}
					color="success"
					onClick={() => answer(true)}
				>
					Correct
				</Button>
				<Button
					style={{ width: "50%" }}
					color="warning"
					onClick={() => answer(false)}
				>
					Incorrect
				</Button>
			</div>
		</div>
	)
}

class EditCardState {
	saving = false
	constructor(public currentContent: string) {}
}
type EditCardProps = RouteComponentProps<{
	cardslug: string
	subject: string
}> & {
	cards: Card[]
}
export class EditCard extends Component<EditCardProps, EditCardState> {
	textarea: HTMLTextAreaElement
	constructor(props: EditCardProps) {
		super(props)
		this.state = new EditCardState(this.getCard().content)
	}
	getCard() {
		return this.props.cards.find(
			c => c.slug == this.props.match.params.cardslug,
		)
	}
	getDerivedStateFromProps(
		nextProps: RouteComponentProps<{ cardslug: string }>,
	) {
		console.log("getDerivedStateFromProps", this.props, nextProps)
		if (
			nextProps.match.params.cardslug !== this.props.match.params.cardslug
		) {
			console.log("here")
			return { currentContent: this.getCard().content }
		}
	}
	render() {
		console.log(
			this.getCard().content != this.state.currentContent,
			this.getCard().content,
			this.state.currentContent,
		)
		const subject = this.props.match.params.subject
		return (
			<div
				style={{
					display: "flex",
					flexDirection: "column",
					height: "100%",
				}}
			>
				<BackToOverview subject={subject} />
				<h1
					style={{
						margin: "auto 8px",
						textAlign: "center",
					}}
				>
					{this.getCard().title}
				</h1>
				<Input
					style={{ flexGrow: 1, minHeight: "400px" }}
					type="textarea"
					name="text"
					id="exampleText"
					value={this.state.currentContent}
					onChange={e =>
						this.setState({ currentContent: e.target.value })
					}
					innerRef={r => (this.textarea = r as any)}
				/>
				<ButtonGroup style={{ display: "flex" }}>
					<Button
						color="primary"
						style={{ flex: 1 }}
						onClick={() => this.wrap("§")}
					>
						§
					</Button>
					<Button
						color="primary"
						style={{ flex: 1 }}
						onClick={() => this.wrap("**")}
					>
						**
					</Button>
					<Button
						color="primary"
						style={{ flex: 1 }}
						onClick={() => this.wrap("_")}
					>
						_
					</Button>
					<Button
						color="primary"
						style={{ flex: 1 }}
						onClick={() => this.insert("\\")}
					>
						\
					</Button>
				</ButtonGroup>
				<Button
					onClick={this.save}
					disabled={this.state.saving}
					color="warning"
				>
					{this.state.saving
						? "Saving..."
						: this.getCard().content != this.state.currentContent
							? "Save"
							: "Saved"}
				</Button>
			</div>
		)
	}
	wrap = (char: string) => {
		this.textarea.selectionStart
		let v = this.textarea.value
		v = strSplice(v, this.textarea.selectionEnd, char)
		v = strSplice(v, this.textarea.selectionStart, char)
		const start = this.textarea.selectionStart + char.length
		const end = this.textarea.selectionEnd + char.length
		this.textarea.value = v
		this.textarea.dispatchEvent(new Event("input", { bubbles: true }))
		this.textarea.selectionStart = start
		this.textarea.selectionEnd = end
		this.textarea.focus()
	}
	insert = (char: string) => {
		const start = this.textarea.selectionStart + char.length
		const end = start
		this.textarea.value = strSplice(
			this.textarea.value,
			this.textarea.selectionStart,
			char,
			this.textarea.selectionEnd - this.textarea.selectionStart,
		)
		this.textarea.dispatchEvent(new Event("input", { bubbles: true }))
		this.textarea.selectionStart = start
		this.textarea.selectionEnd = end
		this.textarea.focus()
	}
	save = async () => {
		this.setState({ saving: true })
		await updateCard(
			this.props.match.params.subject,
			this.getCard(),
			this.state.currentContent,
		)
		this.setState({ saving: false })
	}
}

export function CardQuestion({
	card,
	onContinue,
	subject,
}: {
	card: Card
	subject: string
	onContinue: () => void
}) {
	return (
		<div
			onClick={onContinue}
			style={{
				flexGrow: 1,
				display: "flex",
				justifyContent: "center",
			}}
		>
			<BackToOverview subject={subject} />
			<h1
				style={{
					margin: "auto 8px",
					textAlign: "center",
				}}
			>
				{card.title}
			</h1>
		</div>
	)
}

export function BackToOverview({ subject }: { subject: string }) {
	return <Link to={"/" + subject}>Zurück zur Übersicht</Link>
}

export function CardOverview({
	cards,
	info,
	error,
	cardStates,
	subject,
}: {
	subject: string
	cards: Card[]
	info?: string
	error?: string
	cardStates: CardStates
}) {
	return (
		<>
			{info && <Alert color="info">{info}</Alert>}
			{error && <Alert color="error">{error}</Alert>}
			{[1, 2, 3, 4, 5].flatMap(level => (
				<React.Fragment key={"level" + level}>
					<h3>
						Level {level} -{" "}
						<Link to={"/" + subject + "/learn/" + level}>
							learn
						</Link>
					</h3>
					<ul>
						{cards
							.filter(
								c =>
									getCardState(cardStates, c.slug).level ==
									level,
							)
							.map(card => {
								const cardState = getCardState(
									cardStates,
									card.slug,
								)
								const correctCount = cardState.correct.length
								const totalCount =
									correctCount + cardState.incorrect.length
								return (
									<li key={card.slug}>
										<Link
											to={
												"/" +
												subject +
												"/card/" +
												card.slug
											}
										>
											{card.title}
										</Link>
										{" - "}
										<span style={{ color: "lightgrey" }}>
											{correctCount}/{totalCount}
										</span>
									</li>
								)
							})}
					</ul>
				</React.Fragment>
			))}
			<div>
				Total Progress:{" "}
				{cards.reduce(
					(acc, card) =>
						acc + getCardState(cardStates, card.slug).level - 1,
					0,
				)}
				/{cards.length * 4}
			</div>
			<Input
				placeholder="github API token w/ gist"
				onChange={e =>
					localStorage.setItem(
						"learn_gisthub_token",
						e.target.value.trim(),
					)
				}
				defaultValue={localStorage.getItem("learn_gisthub_token") || ""}
			/>
		</>
	)
}

function strSplice(str: string, index: int, what: string, deleteCount = 0) {
	return str.substring(0, index) + what + str.substring(index + deleteCount)
}

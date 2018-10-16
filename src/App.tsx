import React, {
	Component,
	ReactNode,
	MouseEvent,
	TouchEvent,
	PureComponent,
	Props,
	HTMLAttributes,
} from "react"
import { int, V3, V, M4, DEG } from "ts3dutils"
import slugify from "slugify"
import { CardText, Button, Alert, Input } from "reactstrap"
import { Converter } from "showdown"
import _ from "lodash-es"
import { Gists, GistDescriptor } from "./gists"

import ReactDOM from "react-dom"
import contentMarkdown from "../content/graphs.md"
import { Link, Switch, Route, Redirect } from "react-router-dom"
import Container from "reactstrap/lib/Container"

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

async function initSaving(): Promise<{
	[x: string]: { incorrect: string[]; correct: string[] }
}> {
	const gists = await gs.all()
	let saveGist2 = gists.find(gist => gist.description === "learn saves")
	if (!saveGist2) {
		console.log("Creating new gist")

		saveGist = await gs.createGist(
			{ graphs: { content: "{}" } },
			"learn saves",
			false,
		)
	} else {
		console.log("Found existing matching gist " + saveGist2.id)

		saveGist = await gs.getGist(saveGist2.id)
	}
	return JSON.parse(saveGist.files.graphs.content)
}

const cardTexts = contentMarkdown
	.split(/^(?=#[^#])/gm)
	.map(x => x.trim())
	.filter(x => x !== "")
const cardRegex = /^#(.*)$\s*(?:^slug:(.*)$)?([\s\S]*)/m

class Card {
	constructor(
		public readonly title: string,
		public readonly slug: string,
		public readonly content: string,
	) {}
}

const cards: Card[] = cardTexts.map(text => {
	const [, title, slug, content] = text.match(cardRegex)
	return new Card(
		title.trim(),
		slug ? slug.trim() : slugify(title),
		content.trim(),
	)
})

console.log(cards)
interface CardState {
	level: int
	correct: Date[]
	incorrect: Date[]
}
class AppState {
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
export class App extends Component<{}, AppState> {
	public state = new AppState()

	constructor(props: {}) {
		super(props)

		if (localStorage.getItem("save_graphs")) {
			this.setState({
				cardStates: reviveJSONSave(
					JSON.parse(localStorage.getItem("save_graphs")),
				),
			})
		}
		if (localStorage.getItem("learn_gisthub_token")) {
			initSaving()
				.then(levels => {
					console.log("loaded levels from gist")
					this.setState(({ cardStates }) => {
						mergeSaves(cardStates, reviveJSONSave(levels))
						console.log(cardStates)
						return { cardStates }
					})
				})
				.catch(console.error)
		}
	}

	public render() {
		if (this.state.redirect) {
			const result = <Redirect push to={this.state.redirect} />
			this.state.redirect = undefined
			return result
		}
		return (
			<Container style={{ height: "100%" }}>
				<Route
					path="/card/:cardslug"
					render={match => [
						<Link to="/">Back to Overview</Link>,
						<CardCard
							card={cards.find(
								c => c.slug == match.match.params.cardslug,
							)}
						/>,
					]}
				/>
				<Route
					exact
					path="/learn/:level"
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
							return <Redirect to="/" />
						}
						const testCard = _.sample(levelCards)
						return (
							<CardQuestion
								card={testCard}
								onContinue={() =>
									this.setState({
										redirect:
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
					path="/learn/:level/answer/:cardslug"
					render={({ match }) => {
						const card = cards.find(
							c => c.slug == match.params.cardslug,
						)
						return (
							<CardAnswer
								card={card}
								answer={correct =>
									this.answer(correct, card, match)
								}
							/>
						)
					}}
				/>
				<Route
					exact
					path="/"
					render={match => {
						const result = (
							<CardOverview
								cards={cards}
								cardStates={this.state.cardStates}
								info={this.state.info}
								error={this.state.error}
							/>
						)
						this.state.info = undefined
						return result
					}}
				/>
			</Container>
		)
	}

	answer = (correct: boolean, card: Card, match: any) => {
		console.log("answering")
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
			redirect: "/learn/" + match.params.level,
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

	componentDidUpdate() {
		MathJax.Hub.Queue(["Typeset", MathJax.Hub, ReactDOM.findDOMNode(this)])
	}
}

export function CardCard(
	props: { card: Card } & HTMLAttributes<HTMLDivElement>,
) {
	const { card, style, ...htmlAttributes } = props
	return (
		<div {...htmlAttributes} style={{ ...style, padding: "4px" }}>
			<h3 style={{ textAlign: "center" }}>{card.title}</h3>
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
}: {
	card: Card
	answer: (x: boolean) => void
}) {
	return (
		<BackToOverview>
			<div
				style={{
					display: "flex",
					flexDirection: "column",
					height: "100%",
				}}
			>
				<CardCard card={card} style={{ flexGrow: 1 }} />
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
		</BackToOverview>
	)
}

export function CardQuestion({
	card,
	onContinue,
}: {
	card: Card
	onContinue: () => void
}) {
	return (
		<BackToOverview>
			<div
				onClick={onContinue}
				style={{
					flexGrow: 1,
					display: "flex",
					justifyContent: "center",
				}}
			>
				<h1
					style={{
						margin: "auto 8px",
						textAlign: "center",
					}}
				>
					{card.title}
				</h1>
			</div>
		</BackToOverview>
	)
}

export function BackToOverview(props) {
	return (
		<div
			style={{
				display: "flex",
				justifyContent: "center",
				height: "100%",
				flexDirection: "column",
			}}
		>
			<Link to="/">Zurück zur Übersicht</Link>
			{...props.children}
		</div>
	)
}

export function CardOverview({
	cards,
	info,
	error,
	cardStates,
}: {
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
						<Link to={"/learn/" + level}>learn</Link>
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
										<Link to={"/card/" + card.slug}>
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
			{/*  a6f75fadd2cafa535ef37fd6bc9aedabf507b1ee  */}
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

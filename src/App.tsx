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
import _ from "lodash"
import { Gists, GistDescriptor } from "./gists"

import ReactDOM from "react-dom"
import contentMarkdown from "../content/graphs.md"
import { Link, Switch, Route, Redirect } from "react-router-dom"
import Container from "reactstrap/lib/Container"

const converter = new Converter({ literalMidWordUnderscores: true })

const gs = new Gists(localStorage.getItem("learn_gisthub_token"))
let saveGist: GistDescriptor
async function initSaving() {
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
class AppState {
	levels: { [slug: string]: int } = {}
	queue: Card[] = []
	viewFront = true
	redirect?: string
	info?: string
}
export class App extends Component<{}, AppState> {
	public state = new AppState()

	constructor(props: {}) {
		super(props)
		if (localStorage.getItem("learn_gisthub_token")) {
			initSaving()
				.then(levels => {
					console.log("loaded levels from gist")
					this.setState({ levels })
				})
				.catch(console.error)
		}
	}

	queueLearn = (level: int, num: int) => {
		const { levels } = this.state
		const levelCards = cards.filter(
			card => (levels[card.slug] || 1) == level,
		)
		this.setState({ queue: _.sampleSize(levelCards, num) })
	}

	public render() {
		if (this.state.redirect) {
			const result = <Redirect push to={this.state.redirect} />
			this.state.redirect = undefined
			return result
		}
		// prettier-ignore
		return <Container style={{height: "100%"}}>
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
								(this.state.levels[c.slug] || 1) ===
								+match.params.level,
						),
					)
					const levelCards = cards.filter(
						c =>
							(this.state.levels[c.slug] || 1) ===
							+match.params.level,
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
							answer={correct => {
								const newLevel = correct
									? (this.state.levels[card.slug] || 1) +
										1
									: 1
								const newLevels = {
									...this.state.levels,
									[card.slug]: newLevel,
								}
								this.saveLevels(newLevels)
								this.setState({
									levels: newLevels,
									redirect:
										"/learn/" + match.params.level,
								})
							}}
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
							levels={this.state.levels}
							info={this.state.info}
						/>
					)
					this.state.info = undefined
					return result
				}}
			/>
		</Container>
	}
	saverController = new AbortController()
	saveLevels = _.throttle(
		(newLevels: { [x: string]: number }): void => {
			this.saverController.abort()
			gs.editGist(
				saveGist.id,
				{
					graphs: {
						content: JSON.stringify(newLevels, undefined, "\t"),
					},
				},
				{ signal: this.saverController.signal },
			)
				.then(() => console.log("saved levels"))
				.catch(err => {
					throw new Error(err)
				})
		},
		30000,
		{ leading: false, trailing: true },
	)

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
	levels,
	info,
}: {
	cards: Card[]
	levels: { [slug: string]: int }
	info?: string
}) {
	return (
		<>
			{info && <Alert color="info">{info}</Alert>}
			{[1, 2, 3, 4, 5].flatMap(level => (
				<React.Fragment key={"level" + level}>
					<h3>
						Level {level} -{" "}
						<Link to={"/learn/" + level}>learn</Link>
					</h3>
					<ul>
						{cards
							.filter(card => (levels[card.slug] || 1) == level)
							.map(card => (
								<li key={card.slug}>
									<Link to={"/card/" + card.slug}>
										{card.title}
									</Link>
								</li>
							))}
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

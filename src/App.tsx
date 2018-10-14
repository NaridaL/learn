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
import { Gists } from "./gists"

import ReactDOM from "react-dom"
import contentMarkdown from "../content/graphs.md"
import { Link, Switch, Route, Redirect } from "react-router-dom"

const converter = new Converter({ literalMidWordUnderscores: true })

console.log("converter.makeHtml('v_1 v_2')", converter.makeHtml("v_1 v_2"))

new Gists(localStorage.getItem("learn_gisthub_token")).all().then(console.log)
// console.log(gists.all())
const cardTextsRegex = /(?:^|(?<=\n))#.+?(?=\n#|$)/g

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
		return (
			<Switch>
				<Route
					path="/card/:cardslug"
					render={match => [
						<Link to="/">Zurück zur Übersicht</Link>,
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
				}
			</Switch>
		)
	}
	saveLevels(newLevels: { [x: string]: number }): void {
		throw new Error("Method not implemented.")
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
						Richtig
					</Button>
					<Button
						style={{ width: "50%" }}
						color="warning"
						onClick={() => answer(false)}
					>
						Falsch
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
				<>
					<h3 key={"level" + level}>
						{level}
						<Button tag={Link} to={"/learn/" + level}>
							Learn
						</Button>
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
				</>
			))}
			{/*  a6f75fadd2cafa535ef37fd6bc9aedabf507b1ee  */}
			<Input
				placeholder="github API token w/ gist"
				onChange={e =>
					localStorage.setItem("learn_gisthub_token", e.target.value)
				}
				defaultValue={localStorage.getItem("learn_gisthub_token") || ""}
			/>
		</>
	)
}

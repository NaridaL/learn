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
import { CardText, Button } from "reactstrap"
import { Converter } from "showdown"
import _ from "lodash"

import contentMarkdown from "../content/graphs.md"
import ReactDOM from "react-dom"

const converter = new Converter()

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
}
export class App extends PureComponent<{}, AppState> {
	public state = new AppState()
	queueLearn = (level: int, num: int) => {
		const { levels } = this.state
		const levelCards = cards.filter(
			card => (levels[card.slug] || 1) == level,
		)
		this.setState({ queue: _.sampleSize(levelCards, num) })
	}

	public render() {
		// return <CardAnswer card={cards[0]} answer={this.answer} />
		// return (
		// 	<CardQuestion
		// 		card={cards[0]}
		// 		onContinue={() => console.log("Hello there")}
		// 	/>
		// )
		if (0 === this.state.queue.length) {
			return (
				<CardOverview
					cards={cards}
					levels={this.state.levels}
					queueLearn={this.queueLearn}
				/>
			)
		} else {
			const card = this.state.queue[0]
			if (this.state.viewFront) {
				return (
					<CardQuestion
						card={card}
						onContinue={() => this.setState({ viewFront: false })}
					/>
				)
			} else {
				return <CardAnswer card={card} answer={this.answer} />
			}
		}
	}
	answer = (correct: boolean) => {
		const card = this.state.queue[0]
		const newLevel = correct ? (this.state.levels[card.slug] || 1) + 1 : 1
		this.setState({
			levels: { ...this.state.levels, [card.slug]: newLevel },
			queue: this.state.queue.slice(1),
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
		<div
			style={{ display: "flex", flexDirection: "column", height: "100%" }}
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
		<div
			style={{
				display: "flex",
				alignItems: "center",
				justifyContent: "center",
				height: "100%",
			}}
			onClick={onContinue}
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
	)
}

export function CardOverview({
	cards,
	levels,
	queueLearn,
}: {
	cards: Card[]
	levels: { [slug: string]: int }
	queueLearn: (level, num: int) => void
}) {
	return (
		<>
			{[5, 4, 3, 2, 1].flatMap(level => (
				<>
					<h3 key={"level" + level}>
						{level}
						<Button onClick={() => queueLearn(level, 8)}>
							Learn 8
						</Button>
					</h3>
					<ul>
						{cards
							.filter(card => (levels[card.slug] || 1) == level)
							.map(card => (
								<li key={card.slug}>{card.title}</li>
							))}
					</ul>
				</>
			))}
		</>
	)
}

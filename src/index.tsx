import { App } from "./App"
import ReactDOM from "react-dom"
import React from "react"
import { BrowserRouter } from "react-router-dom"

ReactDOM.render(
	<BrowserRouter basename="/learn/">
		<App />
	</BrowserRouter>,
	document.getElementById("vcs-root"),
)

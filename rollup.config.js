import sourcemaps from "rollup-plugin-sourcemaps"
import typescriptPlugin from "rollup-plugin-typescript2"
import commonjs from "rollup-plugin-commonjs"
import nodeResolve from "rollup-plugin-node-resolve"
import serve from "rollup-plugin-serve"
import livereload from "rollup-plugin-livereload"
import replace from "rollup-plugin-replace"
import { string } from "rollup-plugin-string"
import json from "rollup-plugin-json"
// import glsl from "rollup-plugin-glsl"
import { terser } from "rollup-plugin-terser"
// import { plugin as analyze } from "rollup-plugin-analyzer"
// import { ufligy, uglify } from "rollup-plugin-uglify"
import * as typescript from "typescript"
import * as fs from "fs"
import * as crypto from "crypto"

const pkg = JSON.parse(fs.readFileSync("package.json"))

function createHtmlExternal() {
	return { type: "js", file: "http:/unpkg.com/foo/bar" }
}

let indexHtml = fs.readFileSync("src/index.html", "utf8")
indexHtml = indexHtml
	.replace(/\[([\w-+_\.]*):([\w-+_\.]*)]/g, (_, dev, prod) =>
		process.env.BUILD == "production" ? prod : dev,
	)
	.replace(
		/src=["']https:\/\/unpkg.com\/([^@]+)@\[version]([^"']+)(["'])/g,
		(srcAttribute, moduleName, path, quote) =>
			srcAttribute +
			"\n\t\t\tintegrity=" +
			quote +
			calcSha512Hash("node_modules/" + moduleName + path) +
			quote,
	)
	.replace(/https:\/\/unpkg.com\/([^@]+)@\[version]/g, (substr, pkg) => {
		return substr.replace(
			"[version]",
			require(pkg + "/package.json").version,
		)
	})
// console.log(indexHtml)
fs.writeFileSync("index.html", indexHtml, "utf8")

function calcSha512Hash(file) {
	return (
		"sha512-" +
		crypto
			.createHash("sha512")
			.update(fs.readFileSync(file))
			.digest("base64")
	)
}

export default {
	input: __dirname + "/src/index.tsx",
	output: {
		format: "iife",
		file:
			__dirname +
			(process.env.BUILD == "production"
				? "/bundle.min.js"
				: "/bundle.js"),
		sourcemap: true,
		name: "spaces",
		globals: {
			react: "React",
			"react-dom": "ReactDOM",
			reactstrap: "Reactstrap",
			showdown: "showdown",
		},
		// globals: moduleName => {
		// 	const x = require(moduleName + '/package.json').umdGlobal || pkg.umdGlobals && pkg.umdGlobals[moduleName]
		// 	console.log(moduleName, x)
		// 	return x
		// },
	},
	external: [
		"react",
		"react-dom",
		"react-transition-group",
		"reactstrap",
		"showdown",
	],
	plugins: [
		nodeResolve({
			// the fields to scan in a package.json to determine the entry point
			// if this list contains "browser", overrides specified in "pkg.browser"
			// will be used
			mainFields: ["module", "main", "jsnext", "browser"], // Default: ['module', 'main']

			// not all files you want to resolve are .js files
			extensions: [".js", ".json"], // Default: ['.js']

			// whether to prefer built-in modules (e.g. `fs`, `path`) or
			// local ones with the same names
			preferBuiltins: false, // Default: true

			// Lock the module search in this path (like a chroot). Module defined
			// outside this path will be mark has external
			//   jail: '/my/jail/path', // Default: '/'

			// If true, inspect resolved files to check that they are
			// ES2015 modules
			//   modulesOnly: true, // Default: false

			// Any additional options that should be passed through
			// to node-resolve
			//   customResolveOptions: {
			// 	moduleDirectory: 'js_modules'
			//   }
		}),
		commonjs({
			// non-CommonJS modules will be ignored, but you can also
			// specifically include/exclude files
			// include: 'node_modules/**',  // Default: undefined
			// exclude: [ 'node_modules/foo/**', 'node_modules/bar/**' ],  // Default: undefined
			// these values can also be regular expressions
			// include: /node_modules/

			// search for files other than .js files (must already
			// be transpiled by a previous plugin!)
			extensions: [".js", ".coffee"], // Default: [ '.js' ]

			// if true then uses of `global` won't be dealt with by this plugin
			ignoreGlobal: false, // Default: false

			// if false then skip sourceMap generation for CommonJS modules
			// sourceMap: false,  // Default: true

			// explicitly specify unresolvable named exports
			// (see below for more details)
			namedExports: {
				react: ["Component"],
				"react-is": ["isValidElementType"],
			}, // Default: undefined

			// sometimes you have to leave require statements
			// unconverted. Pass an array containing the IDs
			// or a `id => boolean` function. Only use this
			// option if you know what you're doing!
			// ignore: [ 'conditional-runtime-dependency' ]
		}),
		json(),
		string({
			include: "./**/*.md",
		}),
		replace({
			"process.env.NODE_ENV": JSON.stringify(
				process.env.BUILD || "development",
			),
		}),
		sourcemaps(),
		// glsl({
		// 	// By default, everything gets included
		// 	include: "/**/*.glslx",

		// 	// Undefined by default
		// 	// exclude: ['**/index.html'],

		// 	// Source maps are on by default
		// 	// sourceMap: false
		// }),
		typescriptPlugin({
			typescript,
			tsconfig: __dirname + "/tsconfig.json",
			declaration: false,
			sourcemap: true,
		}),
		process.env.BUILD == "production" &&
			terser({
				compress: {
					passes: 3,
					unsafe: true,
					ecma: 7,
				},
				toplevel: true,
				mangle: {
					// properties: { regex: /^_/ },
				},
				// output: {
				// 	beautify: true,
				// }
			}),
		process.env.ROLLUP_WATCH &&
			serve({
				contentBase: "..",
				open: true,
				openPage: "/learn/",
				host: "localhost",
				port: 10002,
				historyApiFallback: "/learn/index.html",
			}),
		process.env.ROLLUP_WATCH && livereload(),
		// process.env.BUILD == "production" && analyze(),
	].filter(x => x),
	onwarn: function(warning, warn) {
		if ("THIS_IS_UNDEFINED" === warning.code) return
		// if ('CIRCULAR_DEPENDENCY' === warning.code) return
		warn(warning)
	},
}

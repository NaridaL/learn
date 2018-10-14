import * as querystring from "querystring"
export interface ShortFileDescriptor {
	filename: string
	type: string
	language: string
	raw_url: string
	size: number
}
export interface FileDescriptor extends ShortFileDescriptor {
	content: string
	truncated: boolean
}
export interface UserDescriptor {
	login: string
	id: number
	node_id: string
	avatar_url: string
	gravatar_id: string
	url: string
	html_url: string
	followers_url: string
	following_url: string
	gists_url: string
	starred_url: string
	subscriptions_url: string
	organizations_url: string
	repos_url: string
	events_url: string
	received_events_url: string
	type: string
	site_admin: boolean
}
export interface ShortGistDescriptor {
	url: string
	forks_url: string
	commits_url: string
	id: string
	node_id: string
	git_pull_url: string
	git_push_url: string
	html_url: string
	files: {
		[fileName: string]: ShortFileDescriptor
	}
	public: boolean
	created_at: string
	updated_at: string
	description: string
	comments: number
	user: null
	comments_url: string
	owner: UserDescriptor
	truncated: boolean
}

export interface GistDescriptor extends ShortGistDescriptor {
	files: {
		[fileName: string]: FileDescriptor
	}
	owner: UserDescriptor
	truncated: boolean
	forks: {
		user: UserDescriptor
		url: string
		id: string
		created_at: string
		updated_at: string
	}[]
	history: {
		url: string
		version: string
		user: UserDescriptor
		change_status: {
			deletions: number
			additions: number
			total: number
		}
		committed_at: string
	}[]
}

export class Gists {
	getGist(gist_id: string): Promise<GistDescriptor> {
		return fetch(
			"https://api.github.com/gists/" +
				gist_id +
				"?" +
				querystring.stringify({ access_token: this.token }),
		).then(r => r.json())
	}
	editGist(
		gist_id: string,
		files: {
			[filename: string]: { content?: string; filename?: string | null }
		},
		fetchOptions: RequestInit = {},
	): Promise<GistDescriptor> {
		return fetch(
			"https://api.github.com/gists/" +
				gist_id +
				"?" +
				querystring.stringify({ access_token: this.token }),
			{
				...fetchOptions,
				method: "PATCH",
				body: JSON.stringify({ files }),
			},
		).then(r => r.json())
	}
	constructor(
		// public readonly username: string,
		public readonly token: string,
	) {}

	public all(since?: string): Promise<ShortGistDescriptor[]> {
		return fetch(
			"https://api.github.com/gists?" +
				querystring.stringify({ access_token: this.token, since }),
		).then(r => r.json())
	}

	public createGist(
		files: { [fileName: string]: { content: string } },
		description?: string,
		isPublic?: boolean,
	): Promise<GistDescriptor> {
		return fetch(
			"https://api.github.com/gists?" +
				querystring.stringify({ access_token: this.token }),
			{
				method: "POST",
				body: JSON.stringify({ files, description, public: isPublic }),
			},
		).then(r => r.json())
	}
}

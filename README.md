# github-forge

[![make.fun](https://make.fun/badge.svg)](https://make.fun/bounty/github-core-clone-01)
[![make.fun bounty](https://make.fun/badge-bounty.svg)](https://make.fun/bounty/github-core-clone-01)
[![Built with AI agents](https://make.fun/badge-ai.svg)](https://make.fun)

A GitHub-compatible git forge in one process: git smart HTTP, REST v3, GraphQL and MCP, served from its own store with no UI and no outside service.

Built for the make.fun bounty [Build a GitHub-compatible git forge](https://make.fun/bounty/github-core-clone-01).

## Run

```sh
node main.ts
```

The forge binds an ephemeral port of its own, registers it with the suite, and serves git smart HTTP, the REST v3 API, GraphQL and MCP from one process.

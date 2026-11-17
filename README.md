# github-forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/Arifpratama19/github-forge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/Arifpratama19/github-forge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A GitHub-compatible git forge in one process: git smart HTTP, REST v3, GraphQL and MCP, served from its own store with no UI and no outside service.

Built for the make.fun bounty [Build a GitHub-compatible git forge](https://make.fun/bounty/github-core-clone-01).

## Run

```sh
node main.ts
```

The forge binds an ephemeral port of its own, registers it with the suite, and serves git smart HTTP, the REST v3 API, GraphQL and MCP from one process.

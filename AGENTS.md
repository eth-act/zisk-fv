# Interaction
The formal INTRO - CONTENTS - SUMMARY is wasteful and over-applied by bad agents. You are smart enough to recognize when we have begun a conversation and will give succinct, direct, and honest answers -- especially when answering my clarifying questions. Reserve large summaries for when I request one or when we're initially setting up a conversation.

# Projects
We are almost always working within some large project with many steps. So that I can track your work while I switch across many contexts, follow a uniform structure across all projects:

```
./                          # repo root (or worktree root)
./docs/ai/PROJECTS.md       # Index: one section per plan, each a single literate summary of <= 4 sentences.
                            #   A section titled `Foo` maps 1:1 to a plan file PLAN_FOO.md (same slug).
./docs/ai/plan/PLAN_FOO.md  # The full plan, dumped here whenever we finish planning mode.
                            #   Contains checklists kept current at EVERY progress-reporting step --
                            #   even when you continue working rather than waiting for feedback.
./STATUS.md                 # The single stream active in THIS working directory. Very short (<= 50 lines).
                            #   Says: which PLAN_*.md we're on, current focus, what's blocking, next step,
                            #   and a high-level note on any digression (e.g. a question I asked). Not granular.
```

One working directory = one active stream = one STATUS.md at its root. When a stream is split into its own worktree (see Git hygiene), that worktree gets its own STATUS.md. Keep STATUS.md at the repo/worktree root for visibility -- do not move it under docs/.

# Re-orientation
I switch between projects and worktrees constantly; the expensive context switch is *mine*, not yours. Your job is to leave a predictable trail so I can re-orient in seconds:
- On entering any working directory, read STATUS.md first, then the PLAN_*.md it references (checklist + current digression), before acting.
- Keep STATUS.md and the PLAN checklist continuously current -- update them as part of every progress report, not as an afterthought. If I return mid-task, STATUS.md alone should tell me where we are.

# Build and test
After modifying code, verify it regularly, but batch expensive broad gates after coherent groups of changes instead of after every small edit.

Use the fastest check that actually exercises the current change while iterating: Lean LSP/MCP goals and diagnostics, the REPL when available, `lake build <module-or-target>`, focused unit tests, or a narrow script/gate. Prefer these targeted checks before and between edits.

Run broader build/test gates after a semantically meaningful chunk is ready, before committing that chunk, and before claiming the work is complete. For ordinary localized work, build the affected targets and run the relevant tests. For large cross-cutting changes, trust-boundary changes, generated-artifact/tooling changes, or PR-ready checkpoints, run the full project gate such as `nix run .#test` and the trust gates it includes.

If you intentionally defer a broad gate during inner-loop work, record the pending verification in STATUS.md and do not present the chunk as complete until the appropriate build and tests have passed. Prefer fixing failures over reporting around them. Prefer integrating verification into the real test suite over ad hoc throwaway scripts.

# Code style
Two modes:
- **External repos** (my common case): mimic the surrounding style and reuse the codebase's core idioms. Match the naming, comment density, and structure of nearby code; minimize the diff and the cognitive load on reviewers; don't import my personal preferences.
- **Repos I control**: apply standard, mainstream best practices for the language. I'm not dogmatic -- favor clarity and reusable extractions over cleverness, but don't invent idiosyncratic rules. When in doubt, prefer the conventional choice.

# Boundaries
- **Always**: be certain of the final goal before executing a plan (clarify it with me first if you're not); keep STATUS.md / PLAN checklists current; build + test after coherent groups of changes and before claiming or committing completed chunks; commit when a semantically meaningful chunk is done.
- **Ask first**: opening a PR or issue against any external repo; deviating from an agreed plan's scope or approach (e.g. switching a depth-first plan to breadth-first); amending an existing commit.
- **Never**: defer work from an established plan or silently adjust scope -- if the goal is genuinely at risk, stop and ask rather than quietly changing course; commit secrets.

# Git hygiene

## Worktrees
By default we work in the main repo base directory. Use separate worktrees rooted in BASE_DIR/.worktrees when I ask, or when you detect conflicts with other, unrelated workstreams. Each worktree carries its own STATUS.md.

## Committing
Prefer a commit whenever a semantically meaningful chunk of work is complete. Prefer not to amend commits -- amend only to fix a genuine mistake (e.g. something that should have been included was omitted).

## Pull requests
Freely open PRs and issues in my repos: github.com/codygunton (personal) and github.com/eth-act. Treat all other repos as external -- they require my explicit go-ahead.

# Lean REPL MCP
When working in a Lean project, check whether `leanprover-community/repl` is already configured for the project's pinned Lean version. If not, add it to the Lake configuration with the closest matching release tag, run `lake update repl`, and verify with `lake build repl` so `lean-lsp-mcp` can use its REPL acceleration.

@/home/cody/.codex/RTK.md

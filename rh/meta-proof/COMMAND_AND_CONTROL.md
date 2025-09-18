### Command and Control (C2)

- Entrypoint: `rh/Proof/Main.lean`
- Structure: `ARCHITECTURE.md`
- Roles: `AGENTS.md`

### Orders format (manager → agents)
- `[ORDER] TRACK=<RS|DF-WP|DF-Comp|EPM> TASK=<short> DETAILS=<1–2 lines>`

### Agent reply per loop
- `[TRACK] status: <in_progress|blocked|completed>`
- `changed: <files>`
- `fixed: <error/lemma>`
- `next: <top error or idle>`
- `blockers: <ID or none>`

### Claim/release to avoid collisions
- Start: `[TRACK] CLAIM: <file or lemma>`
- End: `[TRACK] RELEASE: <file or lemma>`

### Persistence & discipline
- Agents re-read `AGENTS.md` and `COMMAND_AND_CONTROL.md` each session and ACK: `[TRACK] ACK role + files`.
- On deep missing lemma: append one line to `BLOCKERS.md` with file:line, Lean goal, short context, 1-line proposed approach, then STOP.
- Build cadence: run `scripts/clean_build.sh` if needed on macOS; then `lake build`.
- After each local fix: rebuild; if the next top error is outside your track, stop and report.
- Commit style: `git add <files> && git commit -m "fix(track-XYZ): <short>"`.



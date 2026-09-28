# F3 research-note workflow

This directory inherits the repository AGENTS.md.

The user's requested destination for these research rounds is branch
`codex/f3-balance-research-docs`, directory `docs/f3_balance_research/`.

- Read the latest numbered round before continuing; use `notes_roundN.md` for new rounds.
- Preserve historical `research_notes*.md` and other research lines. Do not silently renumber, overwrite, or delete them.
- State hypotheses, proof status, literature inputs, counterexamples, and unresolved prime-existence claims separately.
- Put reusable verification scripts and small result/provenance JSON files alongside the notes. Large datasets require a separate explicit storage decision.
- After a requested round submission, verify the exact remote commit and file contents before reporting success. Do not force-push.
- Do not describe paper derivations, finite tests, documentation commits, or unrelated CI as Lean kernel verification.
- This routing convention is not a scheduled automation or permission for unrelated repository changes.

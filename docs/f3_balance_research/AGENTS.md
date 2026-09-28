# Proof-document conventions

This directory inherits the repository AGENTS.md.

The maintained destination is branch `codex/f3-balance-research-docs`, directory
`docs/f3_balance_research/`. This directory contains thematic mathematical proof
papers rather than research journals.

- Organize content as definitions, precisely stated results, proofs, necessary boundary remarks, and references. Use stable thematic filenames, not numbered research rounds.
- Keep exploratory notes, unsuccessful approaches, research plans, numerical experiment tables, ad hoc verification scripts, logs, and result/provenance JSON files in a local research archive, outside the repository. Do not reintroduce the former round-note publishing workflow.
- Removing scaffolding must not remove a required lemma, hypothesis, definition, dependency, citation, or mathematical counterexample. A complete proof may use named external theorems only with their relevant assumptions and sources stated.
- Do not promote conjectures, heuristic models, numerical observations, or unverified implications into theorem statements. Keep distinct domains and the difference between primes, almost primes, presieved integers, and uniform residue classes explicit.
- Maintain the README index and working cross-references. Consolidate duplicate statements rather than keeping chronological copies.
- Paper proofs and finite calculations are not Lean kernel verification. Do not claim that a Markdown proof or documentation commit is a formalization.
- Preserve Lean sources, toolchain pins, the official audit/verification scripts, CI, and unrelated research directories unless the user separately requests changes to them.
- For requested repository edits, scope the diff to the intended documents, preserve a local copy before removing research material, verify the exact remote commit, and do not force-push or rewrite history.

This convention is not a scheduled task or permission for unrelated changes.

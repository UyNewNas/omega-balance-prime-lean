# F₃ external reuse ledger

This file records external prior-art and reusable formalization checks for the
F₃ completion project. Entries are evidence for reuse decisions; they do not
by themselves count as local kernel verification.

## 2026-09-28 — RUN: consecutive prime blocks in a reduced residue class

### plby/lean-proofs

- Checked repository: `plby/lean-proofs`.
- Exact pin used by this project:
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Exact theorem:
  `src/latest/Util/MaynardTao/BFT/Result.lean`,
  `MaynardBFT.consecutive_primes`.
- Statement strength: for every `m > 0` there is `C > 0`, depending only on
  `m`, such that for every positive modulus `q`, every integer residue
  `a` with `gcd(a,q)=1`, and every index lower bound `N`, there is a
  prime-index start `r >= N` for which the next `m` primes all lie in the
  class `a mod q` and
  `p_{r+m-1} - p_r <= q*C`.
- The theorem is proved in source, not introduced as an axiom. The same file
  contains an upstream `#print axioms` command whose recorded output lists
  only `propext`, `Classical.choice`, and `Quot.sound`; local re-build and
  audit are still required before this project may trust the imported theorem.
- `src/latest/ErdosProblems/Axioms.lean` also contains a proved
  `shiu_consecutive_primes` derived from `maynardTaoBFT`. It gives
  arbitrarily late consecutive prime strings in a coprime residue class but
  does not retain the uniform span bound needed by RUN-2. Decision: keep using
  `MaynardBFT.consecutive_primes`, not the weaker Shiu wrapper.
- Older versioned directories `src/v4.29.1`, `src/v4.30.0`, and
  `src/v4.32.0` still expose `shiu_consecutive_primes` as an axiom, so they
  are not acceptable substitutes for the current proved producer.

### AxiomMath/PrimeGapsLib and FormalPantheon/BoundedGaps

- Checked `AxiomMath/PrimeGapsLib` for consecutive-prime / residue-class
  results. Its public main results formalize bounded consecutive prime gaps
  (e.g. at most 600/246) and the Maynard sieve endgame, but the checked search
  did not expose a theorem matching a prescribed reduced residue class with
  the RUN-2 `q*C_L` span.
- Checked `FormalPantheon/BoundedGaps` with the same target vocabulary; no
  directly matching final theorem was found in the checked scope.
- Decision: do not rebuild Maynard--Tao/BFT from these libraries while the
  stronger exact producer above is available.

## 2026-09-28 — Lake compatibility for the pinned producer

- Exact upstream package file checked:
  `plby/lean-proofs@8822f7d.../src/latest/lakefile.lean`.
- Its `post_update` hook looks for inherited dependencies below
  `pkg.dir/.lake/packages`; in this downstream project the dependencies are
  materialized in the root workspace package directory, causing the observed
  `BoundedGaps package directory does not exist` failure before kernel build.
- Checked Lean/Lake `v4.34.0` source
  `src/lake/Lake/Load/Resolve.lean`: workspace update writes the manifest and
  then runs `ws.packages.forM (·.runPostUpdateHooks)`; dependency resolution
  is arranged in reverse direct-dependency order before recursion. Therefore a
  local compatibility package intended to run first must be declared after
  `lean-proofs-latest` in the root direct-require list.
- No `v4.34` branch or matching upstream fix was found in the checked
  `plby/lean-proofs` branches/PR/issues. This is only a statement about the
  checked scope, not a claim that no external fix can exist.
- Decision: use the smallest downstream compatibility shim, without modifying
  proof source or skipping the upstream patch checks; keep Lean/mathlib pins
  unchanged.

# F3 progress round 19

Baseline source carrier before this round: 75ef096717eee5a0381e3a4c1382d572e7753868.
Default master remains behind the stacked F3 work.

## Completed in this round

New file: OmegaBalance/F3BFTBAdmissible.lean.

It introduces BFTBAdmissible, a local finite-set admissibility predicate matching
the mathematical definition used by AxiomMath/PrimeGapsLib at commit
1faa7b14e82ddebc2772dfb9153922f01b106477, and bftbAffineOffsets.

New audited theorems:
- bftbAffineOffsets_admissible
- bftbAffineOffsets_all_coprime

The admissibility theorem is stronger than the initially planned form:
a.Coprime D is not needed to preserve admissibility under h -> D*h+a.
For a prime p dividing D all transformed offsets lie in one residue class;
for p not dividing D multiplication by D cancels modulo p.
The coprimality hypothesis is used separately to show every D*h+a is coprime
to D, matching the separate step in BFTB Corollary 3.

Both theorems are exported through OmegaBalance.lean and occur exactly once in
scripts/Audit.lean.

## Verification

Verified source head: f90f978614dfb1f19d4d81b2115b4498abc9c3ea.
Lean PR run 36283766786: success.
Factor-sum PR run 36283766791: success.
Axiom audit: 517 declarations, standard Lean axioms only.
Source audit: 74 Lean files.
Audit coverage: 517/517 exactly once.
Finite F3 regression: 144240 checks PASS.

Draft stacked PR: #25.

## Remaining RUN work

The local signed-residue transfer, full-prime-index consecutiveness, span
scaling, infinitude of run starts, affine residue/coprime arithmetic, and affine
admissibility are now formalized.

The remaining large dependency is the consecutive-primes theorem of
Banks--Freiberg--Turnage-Butterbaugh: the finite CRT construction excluding
non-tuple positions in the interval, the transformed tuple hypotheses, the
Maynard--Tao many-prime input, and the maximal-subset step converting this into
genuinely consecutive primes.

Next subtask: formalize the finite CRT exclusion construction and its
compatibility conditions without replacing the missing Maynard--Tao/BFTB
theorem by a weaker AP statement.

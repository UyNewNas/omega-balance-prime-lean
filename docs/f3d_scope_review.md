# F3D relation review

Source commit: `b4c14823d9a97a45770ed42379673d39b5295be6`. All five requested four-file packages (20 files) read in full through immutable `git show`; exact blob IDs, SHA-256, byte/line counts, full theorem excerpts and hypotheses are in `f3d_relation_review.json`. Also fully read frozen AGENTS.md, README.md, F3 task ledger, F3Rational.lean and F3DeeperExamples.lean. No repository edits, Lean execution or kernel claim. PDFs and TeX were not read. The two short POLY/MULTI research archive summaries were additionally read in full (58/70 lines); neither contains an omitted specialization or a repair of the identified gap. A separate source check verified the other three research originals are exact substrings of their full-read package proofs and all 20 F3D package branch blobs match this source; those checks are separate provenance, not extra body reads in this report.

## Result and scope

- Do not exclude by the `f3d/` directory name. `F3(n)=F3D(n,1)` for natural `n>1`; the signed nonsingular version requires `n!=±1`. This is a real, useful interface dependency.
- Input specialization does not specialize the output to `(integer,1)`. Every construction outputs `(P,Q)`. To convert it to `f3Rat(P/Q)`, prove `Q!=0`; to convert it further to original natural `f3`, prove the quotient is a natural integer greater than one. No prime preservation follows.
- All 25 general result IDs remain GENERALIZED_THEORY_PENDING_SCOPE. Their precise statements/hypotheses are recorded, not skipped. Classification, independent-scaling degree lower bounds, finite-field norm degree spectra and stable-degree limits are not automatically current F3 tasks. None of the twenty files or frozen task ledger establishes them as a necessary dependency of INF/COR/DEN/LOG/RUN.
- Accept the interface/domain safeguards and correction records into the current intake. The concrete rational-extension corollaries below are ELIGIBLE_DERIVED_COROLLARY_PENDING_SCOPE. They are not explicit original-F3 goals in the source and are not silently scheduled.

## Concrete narrow corollaries

All displayed `f3` inputs below are natural integers greater than one. The JSON supplies formulas, guards, source IDs and dependencies for each.

1. `F3D-SPEC-POLY-LAYER`: for fixed integer r, `(N,D)=E0(S_{-r}(n,1))` has `N>D>0` and `f3Rat(N/D)=1_{f3(n)=r}`. At r=0, `N=5n^4+22n^2+5`, `D=(n^2-1)^2`; detection is equivalent to `3|n`. Source: F3D-POLY-1.
2. `F3D-SPEC-POLY-ABS-POS`: `f3Rat(-(3n^2+1)/(n^2+3))=|f3(n)|`; `f3Rat((3n^3+3n^2+9n+1)/((n-1)^2(n+3)))=max(f3(n),0)`. These are constructive identities, not lower bounds. Source: explicit parts of F3D-POLY-3.
3. `F3D-SPEC-MULTI-SIGN`: `f3Rat((3n^2-2n+3)/(n-1)^2)=1_{f3(n)>0}`. Source: F3D-MULTI-1.
4. `F3D-SPEC-MULTI-MINMAX`: Cayley coordinates x,y from two such n,m satisfy `v3(mu)=min(f3(n),f3(m))`, `v3(xy/mu)=max(...)`, with `mu=(x^3+3y^3)/(x^2+3y^2)`. Both resulting coordinates exceed one, so inverse Cayley gives unconditionally defined rational F3 identities. Sources: F3D-MULTI-2 and explicit F3D-DEG-4 construction.
5. `F3D-SPEC-DEG-AMPLIFIED`: instantiate the explicit H_k no-cancellation form at `(n,1)` to obtain a pair encoding `k max(f3(n),0)`. At k=2, `f3Rat(-(3n^2+2n+3)/(n-1)^2)=2 max(f3(n),0)`. Source: F3D-DEG-1.
6. `F3D-SPEC-TERN-CONSTRUCTIONS`: explicit three-input coordinate formulas encode gains 1,2,3 times `min(f3(n1),f3(n2),f3(n3))`; pair constructions have upper degrees 9,10,9. Converting a coordinate R back to scalar `f3Rat((R+1)/(R-1))` requires `R!=1`. Exact minimum-degree claims are separate. Sources: constructive parts of F3D-TERN-1/2/3/4.
7. `F3D-SPEC-STABLE-INTERVAL`: the quartic pair encodes gain q=1 or 2 times `1_{a<=f3(n)<a+L}` for fixed L>=1,a in Z. The inverse-Cayley denominator really is nonzero: for the unshifted form `A-B=(3^q-1)(1-3^(2L))u^2v^2<0`. Source: constructive F3D-STABLE-1. No projective-kernel or stable-degree theory is needed for this identity.

## Substantive proof blocker: MULTI-L12

Stable correction ID: `F3D-CORR-MULTI-L12`. Source: `multivariate_tropical/proof.md` §9 (lines 763–771), used in §10 (line 858 onward). It calls each fixed-grid valuation a finite integer tropical expression.

Take m=3 and the globally admissible integer polynomial pair

`P=((n1+d1)-(n2+d2))^2+3(n3+d3)^2`, `Q=0`.

Every legal input has `n3+d3!=0`, so P>0 and P±Q=P. Thus output belongs to D and realizes the constant g=0. Zero second coordinates are permitted by D; this is not a singular-output loophole. It is even nonzero on the corresponding Q3 domain because the two nonzero summands have even versus odd valuations.

For source unit grid `s_i=r_i=1`, allowed because `1∈S_D`, take `n_i=3^t_i+1`, `d_i=3^t_i-1` for all nonnegative t_i. Each input is admissible and F(X_i)=t_i. For every M>=0 the individual grid-value function h has

`h(0,0,M)=2M+1`, but `h(1,0,M)=0`.

Input sup-distance is one. Every finite tropical expression has a finite global Lipschitz constant, so h is not one. The assertion that a finite integer-affine partition is equivalent to a tropical expression lacks a bounded-jump/continuity argument and is false here. The finite-affine-partition half itself is not refuted.

This refutes the intermediate tropical claim, not the main classification: g=0 is itself tropical. It blocks the present MULTI-3 necessity route and thus the universal-realizability part of MULTI-4 as currently justified. MULTI-1/2, tropical sufficiency, and explicit bounded-switch constructions do not depend on this bad step. A possible repair may work directly with grid minima and the uniform interpolation bound; none is supplied here. The narrow boundary review was independently confirmed on 2026-09-30: source metadata and TeX now withdraw the blanket audit label for the affected necessity route. See [the dedicated correction report](../reports/f3d_proof_boundary_corrections.md). This confirms the counterexample and its scope, not a repair or a full theory recertification.

## Other precise corrections

- `F3D-CORR-TERN6-DOMAIN`: the original theorem.md §F3D-TERN-6 omitted `m>=2`, which proof.md explicitly supplied. For m=1 the identity pair has degree one, hence minimum degree at most one, already contradicting the unguarded `3m` lower bound. The guard and boundary witness were added consistently on 2026-09-30; the narrow correction does not recertify the whole degree theory.
- `F3D-CORR-POLY-CLEAR-DENOM`: proof.md §8.1 must choose L clearing the coefficients of both homogenized A and B; integrality of just `2L A,2L B` does not imply integrality of `L(A±B)`. For A=1/2,B=1/4,L=2 the former holds and the latter fails. Taking L more divisible, or doubling the output, repairs this local step. It does not refute the classification.

## Boundary for lower bounds and impossible operations

Degree lower bounds quantify over all common scalings and all unit parts. Fixing d=1, restricting to primes, or asking for scalar outputs changes the candidate class; a new lower-bound proof is needed. The impossibility of computing `F(X)F(Y)` by a polynomial pair is also different from the existing original-F3 theorem that no arbitrary scalar rule H can recover `f3(mn)` from `f3(m),f3(n)`; do not substitute one for the other. The p=2 results and all Omega/F_Sigma themes remain outside this intake.

## Final checks

A finite exact-arithmetic check passed 7,037 restricted-formula instances (149 each for zero detection, absolute value, positive part, sign, and doubled positive part; 1,490 interval instances; 4,802 binary min/max identities). `f3d_specialization_formula_sanity.json` records coverage. These sanity checks do not replace the paper derivations or a Lean proof. The JSON manifest has 27 fully read source files, of which exactly 20 are the requested packages, and 25 unique generalized theorem IDs.

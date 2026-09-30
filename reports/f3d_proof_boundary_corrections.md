# F3D source-proof boundary corrections

Review date: 2026-09-30. Source base: `e59f4e4dc729a12e693594ff4dd996f1bb57f6b9`.

This is a narrow source correction, not a formalization of generalized F3D
classification or degree theory. It introduces no Lean declarations and makes
no kernel-proof, asymptotic, or full-theory recertification claim.

## Sources and scope

The exact `theorem.md`, `proof.md`, `scaffolding.md`, `formalization.md`, and
`paper.tex` files of both packages were read at the source base:

- `docs/proofs/f3d/multivariate_tropical/`
- `docs/proofs/f3d/ternary_minima_norm_forms/`

The initial relation review is retained in
[`docs/f3d_scope_review.md`](../docs/f3d_scope_review.md). Its original immutable
source was `b4c14823d9a97a45770ed42379673d39b5295be6`. The MULTI/TERN Markdown
source hashes are unchanged between that intake and this correction's base;
the reviewed TeX files additionally synchronize the PDF sources.

Only two established boundary findings are applied here. This change does not
schedule the other generalized F3D results or repair the separate POLY
coefficient-clearing issue. Existing constructive identities and their scoped
paper status are preserved.

## F3D-CORR-MULTI-L12: fixed-grid tropical equivalence is false

Original locations: MULTI `proof.md` §9, Lemma 9.1, its use in §10, and
`scaffolding.md` MULTI-L12/L14. A finite integer-affine partition can be
discontinuous across its cells. It is not automatically a finite expression
built from integer affine functions using `+`, `-`, `min`, and `max`.

### Globally legal witness

For three inputs in

\[
\mathcal D=\{(n,d)\in\mathbb Z^2:n\ne\pm d\},
\]

write \(u_i=n_i+d_i\) and set

\[
C=(u_1-u_2)^2+3u_3^2,\qquad P=C,\qquad Q=0.
\]

Since \(u_3\ne0\), \(C>0\) over the integers. Thus \(P+Q=P-Q=C\ne0\),
the output is legal, and the pair realizes the constant function \(g=0\).
The domain permits a zero second coordinate; this is not a zero-valuation
convention or singular-output counterexample.

Take the valid degree bound \(D=2\) and fixed units
\(s_i=r_i=1\in S_2=\{1,4,7\}\). For every nonnegative integer vector
\(\mathbf t\), the source grid gives

\[
n_i=3^{t_i}+1,\qquad d_i=3^{t_i}-1,
\]

with \(F(X_i)=t_i\). The individual grid valuation is

\[
h(\mathbf t)=v_3\!\left(4((3^{t_1}-3^{t_2})^2+3^{2t_3+1})\right).
\]

For every integer \(M\ge0\),

\[
h(0,0,M)=2M+1,\qquad h(1,0,M)=0.
\]

The second equality uses \(4+3^{2M+1}\equiv1\pmod3\). The input
sup-distance is one while the output difference is unbounded.

Every integer affine function has a finite global Lipschitz constant in the
sup-norm. Addition and subtraction add such constants; finite min/max take a
maximum of them. Induction over the finite expression therefore gives a finite
global Lipschitz constant. Consequently this \(h\) is not a finite integer
tropical expression. This all-\(M\) argument is a written mathematical
counterexample, separate from the finite script below.

### Exact status boundary

- Withdraw the tropical-equivalence assertion in MULTI-L12. Preserve the
  original finite-affine-partition discussion without treating it as a
  tropical representation proof; this review neither refutes nor recertifies
  the partition claim.
- Mark MULTI-L14 / MULTI-3 necessity `RESEARCH` with a proof/audit gap. The
  source's step from individual fixed-grid values to tropical grid minima is
  unavailable.
- Preserve MULTI-L13: the valid identity \(g=\eta_A-\eta_B\) follows directly
  from unit-independence of the output and finite minima. It does not by itself
  prove tropicality. The Lagrange bound concerns the grid minimum, not every
  individual grid value.
- Mark the current MULTI-4 route to a Lipschitz bound for all realizable
  functions, and thence polynomial nonrealizability of the unbounded switch,
  `RESEARCH`. No independent repair is asserted here.
- Preserve the original scoped `PAPER-AUDITED` status of MULTI-1/2,
  MULTI-3 constructive sufficiency, finite-tropical Lipschitz bounds, the
  switch's non-tropicality calculation, and the fixed-amplitude switch
  construction. These statements do not use the false step.

This is **not** a counterexample to the main classification: \(A=B=C\), so
the individual jumps cancel in the actual output \(g=0\), which is tropical.
It does not refute discontinuous finite affine partitions or claim that any
realizable output has been shown non-tropical.

## F3D-CORR-TERN6-DOMAIN: restore the m >= 2 hypothesis

The theorem summary omitted a hypothesis already explicit in TERN `proof.md`
§1. The corrected two-sided statement is

\[
3m\le\mathfrak d_m(1)\le m(\lceil\sqrt m\rceil+1),\qquad m\ge2.
\]

At \(m=1\), the identity pair \((P,Q)=(n_1,d_1)\) maps every legal input to
itself and has total degree one. Hence \(\mathfrak d_1(1)\le1<3\), which
already contradicts the unguarded lower bound. No exact degree lower-bound
classification is needed for this correction. The empty-input minimum is not
part of the statement either.

The guard is explicit in the theorem, proof overview and grouped-norm section,
scaffolding, formalization map, TeX, and README reference. TERN proof Lemma 5.1
also states the same `m >= 2` hypothesis that its original coordinate-factor
argument already uses, with `k >= 1` explicit. The finite-field constructions,
9-10-9 spectrum, and general lower-bound arguments are not recertified here;
their previous scoped paper statuses are preserved.

## Reproducible finite certificates

Run:

```sh
python3 scripts/check_f3d_proof_boundaries.py > reports/f3d_proof_boundary_check.json
```

The standard-library script uses exact integer arithmetic and rejects zero
arguments to its valuation function. It passes:

- 65 adjacent valuation pairs, `M = 0,...,64`, checking both values, legal
  input/output, constant realized output zero, and sup-distance one
- 19,683 MULTI unit-grid instances, all six units in `{1,4,7}` and each of the
  three depths in `{0,1,2}`, checking admissibility and output zero
- 1,600 signed legal TERN identity inputs with coordinates in `[-20,20]`, plus
  the explicit degree-one monomial support and the comparison `1 < 3`

The machine-readable result is
[`f3d_proof_boundary_check.json`](f3d_proof_boundary_check.json). These finite
certificates are regression evidence only. They do not prove an all-parameter
or asymptotic theorem, repair MULTI necessity, certify degree lower bounds, or
constitute Lean kernel verification.

## Verification and PDF validation

Local checks against the revised source:

- `python3 scripts/check_sources.py`: PASS, 96 Lean files and no proof escapes
- `python3 scripts/check_audit_coverage.py`: PASS, all 620 project declarations
  covered exactly once
- finite certificate regeneration: PASS
- `git diff --check`: PASS
- `python3 scripts/verify.py`: blocked before Lean execution, exit 2 because
  `lake` is unavailable; no full-verification or exact-head CI claim
- local XeLaTeX attempt: blocked because `xelatex.fmt` is absent and the default
  format-cache location is read-only; no successful PDF build/render claim

Both `paper.tex` sources contain the corrections. The committed `paper.pdf`
binaries are deliberately untouched in this source-only commit. They must be
rebuilt by the existing `build-proof-pdfs.yml` workflow on the publication
branch, then checked against the revised source and rendered for inspection.
An older PDF is not evidence that these corrections were built. Publication,
CI, generated-PDF commits, and final render inspection remain pending at this
report's source-commit stage.

No Lean source, audit registration, pinned dependency, workflow, or other
worktree was modified.

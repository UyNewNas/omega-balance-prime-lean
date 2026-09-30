# F₃ proof intake and pending formalization ledger

Locked source snapshot: `b4c14823d9a97a45770ed42379673d39b5295be6` on `master`;155 branch heads,41PRs. This scan does not certify Lean completion.

## Scope and verification

- GitHub branch pagination:100+55; PR listing41; PR22 commit pagination100+34. All496 unique retrieved PR commits and parent lists match the non-shallow cloud clone.
- All32 current `docs/proofs/f3/*/{theorem,proof,scaffolding,formalization}.md` files are fully read. Unmerged WAV adds4 files at311b0a22.
- Stable package IDs:36. Additional source-group keys are provisional; HIER/MOM/REC transports are deduplicated.
- Exact assumptions, source commit/blob, DAG, proposed interfaces and dependency boundaries are in `f3_proof_intake.json`.
- Existing Ω/FΣ/PR5 work is excluded. Five F3D packages have a separate completed relation audit for original-F3 specializations; their full source bodies are now read; formalization scope is not automatically expanded.

## Corrections and changed boundaries

- ROOT4 full-family normalization needs4/729 instead of2/729: simultaneous negation gives the missing equal residue branch. The correction is being handled separately in PR43. Local PAT is unaffected.
- WAV1 has a false intermediate size bound; a product-factor divisibility argument repairs the proof without changing its theorem.
- MOM range is the improvedη<1/(q−1), with all-prime product injectivity and ultra-deep tail. Its old scaffold IDs changed meaning; use current files.
- ROOT arbitrary-p-adic depths need extended valuation at0 or explicit exclusions. Preserve all positive/nonzero conditions in the integer Lean API.
- MOM/REC prerequisite `prime_product_correlations.md` exists only on a1a724b6 work branch at this snapshot; master links do not resolve.

## Accepted stable proof groups

- F3-PAT-1: LocalL1–L3 can be independent; globalGT complexity≤2 remains separate
- F3-HI-1–3: Local three-factor algebra, finite roots/counting, finite patterns;GT/GTZ prime transfer
- F3-HIER-1–3: q=3^s,total-degree rigidity and coefficient-sum dichotomy;general finite-complexity prime transfer
- F3-ROOT-1–4: Quadratic roots, finite inverse/counting;ROOT4 normalization correction first
- F3-MOM-1–4: Uniform tails, weighted moments, covariance recovery, rational PGF
- F3-PEAK-1–4: Effective second-peak separation and sparse supercritical peaks
- F3-WIN-1–6: Sliding-window capacities, removed maxima and integer covariance
- F3-REC-1–5: Unequal-depth certificates, waiting times, passive lower bound, capped recovery
- F3-WAV-1–6: Finite stationary phase, wavelets, AP/divisor bounds;single-prime transfer only

## Additional located proof sources

- F3-BRANCH-ARITH: `docs/f3_balance_research/arithmetic.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 sign/power depth; §2 opposite-layer/gap/twin identities; §3 sharp perfect-power bound; §4 inverse-factor equal level; §5 finite Liouville identities and elementary depth tail. Elementary valuation identities/inequalities; finite Liouville count is identity, not prime existence.
- F3-BRANCH-FIX: `docs/f3_balance_research/F3_fixed_gaps.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 deterministic gap classification; §2 square/isometric coordinate; §3 uniform coordinate; §4 joint tail; §5 boundedness; §6 one-prime AP count/composite companions. Hensel and fixed-modulus PNT/Dirichlet are external. §6 requires only p prime, never p+hi. Finite local patterns can be realized with all companions composite. Fixed shifts/thresholds before X→∞.
- F3-BRANCH-DIL: `docs/f3_balance_research/prime_dilations.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §2 exact LF input/local factors; §3 deterministic three-way lift+finite layers; §4 five-prime asymptotic; §5 explicit shape. External GT+GT nilsequence+GTZ inverse theorem for five forms complexity≤3; all parameters fixed. Variable prime dilation d, not fixed prime gap.
- F3-BRANCH-ROOTM: `docs/f3_balance_research/prime_product_correlations.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §2 roots/distance matrix; §3 compatible tail+exact profile+≤3 obstruction+maximum; §4 all-prime transfer+TV; §5–7 realizations. W>0 unit and for all-prime transfer divisible by primes≤N other than3; all fixed shape and precision. LF external; TV convergence is absolute, not growing-depth relative asymptotic or moment convergence.
- F3-BRANCH-QW: `docs/f3_balance_research/quadratic_weights.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 stationary phase/discriminant; §2 two-branch Haar wavelets; §3 AP/divisor bounds; §4 active shifts/window; §5 one-prime mean. r≥1; zero defined by divisibility W(0)=2. Short window2≤H<3^(2r−1)−2. Prime mean needs PNT/Siegel-Walfisz, only input p prime.
- F3-BRANCH-SPEC: `docs/f3_balance_research/spectral_kernels.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 characters/Fourier; §2 projections/eigenvalues; §3 short-band matching and sharp threshold; §4 CRT local sieve. Unnormalized counting inner product; kernel not PSD (5,97 gives−2 at r3). Spectral facts do not establish prime positivity.
- F3-BRANCH-INV: `docs/f3_balance_research/inverse_geometry.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 depth boundary; §2 all layers quadratic normal form; §3 box/slant-line limit; §4 exact square/single-sided box; §5 local roots. Not prime endpoints. Both endpoints<m essential; (17,143),m81 violates depth boundary if removed. Uniform area error cannot beo(√m).
- F3-BRANCH-SIEVE: `docs/f3_balance_research/sieve_bounds.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 Kloosterman completion; §2 merged congruence rectangles; §3 Selberg; §4 prime depth tails. External Kloosterman-Weil/Selberg/multiplicative mean. Upper bounds only, not prime/twin lower bound.
- F3-BRANCH-PRE: `docs/f3_balance_research/presieved_geometry.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 divisibility; §2 fundamental lemma; §3 line-phase; §4 area regimes; §5 bounded almost primes; §6 finite sieve phases. Presieved integers/almost primes, not all-three-prime result. Fixedc positive chord needed for relative line asymptotic; area regimec/√r→∞ or fixed exponent margin. Fundamental lemma external.
- F3-BRANCH-LIO: `docs/f3_balance_research/rough_liouville.md` at `a1a724b6083e223ee407046c17dc8c90b036150f`; §1 fixed external bounds; §2 uniform main term; §3 wider negative sign. External Thorner-Zaman fixed-kernel PNT exponent5/12 and Xi-Zheng v2 Brun-Titchmarsh envelope; no n±2 primality. X0 ineffective/unspecified. Full source/version check still needed.

## Current scan limits

The locked original-F3 source intake is complete: 155 branch graphs, 41 PRs, 36 stable proof IDs, all 32 master four-file F3 sources, 4 unmerged WAV files, 13 thematic sources, and the 15-file historical research sweep plus 4 exact package-source duplicates. Per-branch F3-scoped watermarks are recorded in JSON. The separate F3D relation review now completes source reading, with all 25 IDs recorded. Generalized theory scope and independent correction audits remain pending.
No new proof is marked Lean-proved by this intake. Use the exact-head complete gates for any subsequent implementation.


## Additional master research intake

- F3-MASTER-NET: first-rise graphs, exact maximum-weight-forest tail probabilities, forest independence and finite monomial depth laws
- F3-MASTER-LEAVEONE: leave-one-product depth cap, conditional m-wise independence, Smith-form and unit-coordinate inclusion-exclusion counts; this is distinct from the packaged HI theorem despite the filename
- F3-MASTER-AFFINE: original F3 affine Haar/integer Cesàro kernel, with periodic truncation and L²-tail passage; some rational/log/ordinary-product APIs already exist and should be reused
- Historical journal aliases: exact finite/arithmetic residuals from seven research rounds. Route overlaps to WAV, ARITH, QW, SPEC, INV, SIEVE, PRE and LIO first; retain stronger boundaries, explicit constants, twin-candidate sieve identities and unmatched claims. Open twin/neighbor-prime lower bounds are excluded

All exact statements, assumptions, proof sections, source blobs, external inputs, open exclusions and deduplication routes are preserved under master_research_inventory. These archives have located written proofs, not automatic PAPER-AUDITED or Lean-proved status.


## F3D source-review supplement

`f3d_relation_review.json` and `.md` record all 20 full-read package files, 25 generalized IDs, the accepted input/domain bridge, seven eligible narrow derived corollaries, and three precise correction records. Source reading is complete; generalized theory scope is pending. The MULTI-L12 fixed-grid tropical assertion has a substantive proof gap, TERN6 needs m≥2, and POLY denominator clearing needs a stronger integer multiplier. These findings do not certify or refute the full generalized main classifications.

## 已接入实现与广义范围

PAT局部L1–3已通过代码5f94116a全门禁并合入59be8b23；ROOT4归一化修正已合入ad603cf4。精确后续状态见JSON implementation_updates，不改写来源快照。五个F3D包20文件已完整读完，25个广义结果未自动扩入本工程；输入F3(n)=F3,D(n,1)桥、输出域守卫及三个纠错线索已接收。七个有理输出特化是候选而非已承诺任务。详见 [范围与纠错报告](f3d_scope_review.md)。未把广义主分类的中间引理缺口说成原主分类反例。

## 2026-09-30：REC 有限精度实现增量

已接收 F3-REC-4 的同一纸面来源（PR #41，b4c14823，proof blob ef55306b）进入
确定性截断矩阵实现候选 `F3RootTruncatedReconstruction.lean`。初次实现完整重读四件套；
工作区更换后从原始写入记录恢复同一 Lean blob 4a24db55453664e08976cd883757912c874f1adb，
文档在 master f50d2366 增量接回。没有新增数学来源、改动原有扫描水位或把扫描完成
混同形式化完成。当前 11 条候选精确声明、完整定义域、REC-L11 / 截断 REC-L5 节点
和未闭合概率层见 [REC 映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l11--截断-rec-l5-有限矩阵候选尚未执行-lean)
与 [持续任务](f3_formalization_tasks.md#2026-09-30rec-l11--截断-rec-l5-有限矩阵候选)。
恢复后源码与一对一审计重新通过；这不升级为 LEAN-PROVED，新精确 head 完整 CI 仍待执行。

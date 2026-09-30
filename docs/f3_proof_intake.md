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
和未闭合概率层见 [REC 映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l11--截断-rec-l5-有限矩阵已通过精确-ci)
与 [持续任务](f3_formalization_tasks.md#2026-09-30rec-l11--截断-rec-l5-有限矩阵候选)。
恢复后的源码与覆盖检查本身不构成内核证明；其后的独立精确CI记录如下。

本批代码564bb498已在精确push36671721342与PR36671762437通过全部门禁；641条声明仅标准公理，98源文件与覆盖通过。只更新确定性截断矩阵/阈值关系的Lean覆盖，原始来源水位与概率节点保持不变。


## 2026-09-30 07:30 UTC bounded refresh and REC finite-batch implementation

After the 07:28 full fetch, 165 actual remote branch heads were compared with
the original intake watermark: among original sources only master changed
to `0bd5333e92b429306ffb139728c04cd4a1ee796b`; original research heads are
unchanged. The all-issues query updated since 06:38 returned only our PR47/51.
No new external paper intake was found in this bounded refresh. Original
mathematical source watermarks remain unchanged; this does not claim another
full reading of every research file.

The existing REC four-file package was reread for the next implementation
slice: theorem 2.3 / equation (2.7), using theorem 2.1 / (2.3) and the existing
Proposition 2.2 scan. `F3RootBatchHaar.lean` adds 10 candidate declarations for
actual fixed-root finite-batch probability under the genuine finite product
of unit Haar measures, including T=0 and the unchanged scan/model wrappers.
This is a new implementation of an already accepted source, not a new paper
or source-watermark advance. Local 694+1 coverage, source and finite checks
are not kernel validation; new exact-head CI remains pending. Infinite
waiting time, its mean, moving random configurations, union bounds and prime
sampling remain open. [Exact scope](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l6-fixed-root-finite-batch-candidate).

## 2026-09-30 08:17 UTC：固定根有限批次概率已通过精确 CI

代码 `c863b99d1ba71c4a63e9b555e36bb457e0918bef` 的
[push 36684973082](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36684973082) 与
[PR 36685062948](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36685062948)
全部通过。实际公理日志为695项（694条项目声明+1条必需上游产生器），仅标准三公理；
106个项目源文件、650个依赖源码/固定版本检查、一对一覆盖、内核回归、
144240有限检查均成功。独立专项源码/数学复核确认实际归一化 Haar、真实有限乘积、
共享单次参数、T=0及既有扫描接口，没有循环概率假设。

本节只升级 `F3RootBatchHaar.lean` 已列出的10条声明，得到固定实际单位根的
有限批次失败/扫描未知概率 `(1-3^(-L))^T`。原始完整配置的固定模型包装保留全部
前提和无限根点；未构造无限单边等待变量、未证明其均值、移动随机配置、
多对联合恢复界或素数传递。此前 candidate/pending 文字是实现历史。
最终文档提交仍单独执行完整CI，原始 proof 来源水位不因本次实现而改变。

## 2026-09-30：实际一基等待时间候选（固定根）

本候选基于已验证批次主线33ccdfe，新增 `F3RootWaitingHaar.lean`。
`f3UnitHaarStream` 是实际 `Measure.infinitePi` 单位 Haar 乘积；
`f3RootWait` 是对真实“不等深度”事件调用库的 `hittingAfter`，从下标0开始再加1，
值域 `ENat = WithTop Nat`。从不出现证书时仍为∞，没有通过 toNat 把∞改成0。

候选逐点证明 T<τ 等价于前T次全部失败，包括T=0；把该事件识别为实际有限柱集，
再由已有单次Haar律计算几何尾概率。τ本身逐点等于尾指标的非负级数，包括∞情形；
可测性、非负积分交换和库几何级数给出实际期望 `∫⁻τ=3^L`，再推出几乎处处有限。
没有预设几何分布、概率公式或同次观测的根标签独立性。

纸面映射：REC-L6 / 定理2.3式(2.7)的固定根与固定原配置部分。
此处没有证明移动随机配置、联合矩阵停止界、完整有符号差律、被动下界或素数传递。
原配置包装保留正b、m≥2、互异同模3单位根；观测为超额深度R。

代码和12个Audit条目目前为未编译候选，本地源码107文件、706条项目声明+1产生器
覆盖检查通过，不能替代精确CI。有限二元前缀回归共1533个带权样本，验证一基计数、
T=0、从未命中的有限前缀语义、几何尾及截断期望；不是无限采样证明。
最终接入最新主线及新的完整Actions门禁仍是接受条件。

未引入新纸面来源；沿用既有REC来源和原始水位，不把此候选计为LEAN-PROVED。

## 2026-09-30: narrow WAV discriminant proof-step repair

`F3-WAV-1-PROOF-BOUND` now has an imported paper correction and a local Lean
code candidate, awaiting exact-head CI. The source four-file package remains
fixed at `311b0a226c0a64854f495dd3d1561fefaf6cb6e6`; its research branch is not
changed. The false statement `h²−4<3^(2r−1)` fails at `r=2,h=10,H=10`
(`96<27` is false). The corrected argument bounds the two factors separately
and reuses prime-power divisibility; the original theorem and strict window stay
unchanged. General transfer inherits integer `h`, `r≥1`; only the short-window
lemma takes `r≥2`, `2<h<3^(2r−1)−2`. The zero case `h=2` is separate, and the
first excluded point has valuation `2r−1` and weight `−1`.

The candidate is one general declaration and four existing-target kernel
regressions, all in Audit. Source guard 106 files, coverage 689 project
statements plus one required external producer, six audit-guard tests and
199262 finite interior checks pass locally. `verify.py` exits 2 before Lean
stages because Lake is absent; none of those passes is kernel verification.
Full WAV1 conditional transfer and WAV2–6 remain incomplete. The source directory
has no PDF or TeX; its broken PDF link is replaced with a factual missing-artifact
note, with no generation/render claim. See the
[exact mapping](proofs/f3/wavelet_transfer/formalization.md),
[source/correction evidence](../reports/f3_wavelet_bound_correction.json), and
[reuse gate](f3_external_reuse.md#2026-09-30-f3-wav-1-proof-bound-target-first-reuse-gate).

## 2026-09-30 09:03 UTC：WAV 短窗口修复已通过精确内核验证

代码 `c7e5d7d55209e575cc1449cf4595762f63469cf2` 的
[push 36690453078](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690453078) 与
[PR 36690460110](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690460110)
全部成功：700项公理审计（699条项目声明+1必需产生器）仅含标准公理，
107个项目源文件、650个依赖模块及固定版本检查、完整覆盖、构建和回归均通过。
一般非整除引理与四个边界回归均有实际公理输出；独立数学/源码复核通过。

只升级 `F3-WAV-1-PROOF-BOUND`：严格窗口的整数判别式非整除、r=2/h=10旧大小界
反例及其正确结论、h=2零判别式、h=25排除端点的精确整除层/权重回归。
不宣告整个条件传递或WAV2–6已形式化，不把源PAPER-AUDITED归属解释为本次全包再审计。
首轮未限定dvd_sub的失败已据固定Lean4.34 API改为Int.dvd_sub，公开命题没有改变。

最终树另合入已验缓存工作流主线ef68dc4，数学源码与上述已验版本字节相同；
仅更换缓存保存范围，所有内核/源码/公理门禁保留。这个组合/文档头仍单独执行CI。

## 2026-09-30 09:23 UTC：等待时间首轮 CI 诊断与主线组合

候选0b80102d的push36691409632和PR36691460119均在新等待模块失败；实际RUN产生器
已构建，但后续公理/回归/覆盖门禁未完成，不能据此认定等待律已证明。固定版本中ENat
是WithTop Nat的类型定义而非可自由混用的缩写；修复将实际hittingAfter结果显式标成ENat，
使用ENat专用recTopCoe及自然数嵌入比较API，并调用实际常函数指标的积分变体。
所有公开结论、无限值、原模型及概率前提不变。

同时真实三方接入主线7d94cf69，完整保留已验WAV五条声明与默认分支缓存保存工作流。
组合源码108文件、711条项目声明+1必需上游产生器的一对一覆盖及六项审计规则测试通过；
这些只是预检，组合仍须新的精确CI。09:11读取169个实际远端分支并检查近期PR/issue，
原研究来源头未变，新增记录仅为本轮工程PR；不更改原始proof水位或提升未验任务状态。

## 2026-09-30 09:40 UTC：实际固定根等待律已通过完整内核验证

代码0255c6b55f44ecb2fc7ee69a376969f655ac4e83，树3430edd9b9f09b4663e6018c8ec07a72b8c1d07e，
[push36697262997](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697262997)和
[PR36697267202](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697267202)
均完整成功。12条新声明分别输出仅propext、Classical.choice、Quot.sound；全部712项
公理输出（711项目+1必需产生器）、108项目源文件、650依赖模块、固定版本、构建、
内核回归、一对一覆盖及144240有限检查通过。独立数学/源码复核和主线保留复核通过。

新增证明对应REC-L6/定理2.3式(2.7)的固定根及固定原配置部分：真实无限单位Haar流上，
一基首次证书时间（从不命中仍为∞）满足实际几何尾律，非负期望3^L，并且几乎处处有限。
逐点尾计数包括∞，没有用预设概率质量替换采样空间。实际原配置保留共同正基深度、
m≥2、互异同模3单位根；截断/联合矩阵停止界、移动配置、有符号差律和素数传递仍未完成。

前三轮编译失败属于类型包装/命名/API匹配：最终使用ENat专用递归、显式类型及
库hittingAfter等价的直接命题组合，避免重写器展开p-adic包装。没有改动公开结论或
前提，也未增加透明度/安全设置。以上是已验代码；本次状态文档头仍另行运行完整CI。

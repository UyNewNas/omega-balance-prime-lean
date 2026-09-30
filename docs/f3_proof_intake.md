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

## 2026-09-30：REC-L7 实现增量

本轮从已合入PR54的 `338442744c906dae107b65e83f010f0b76d71ad2` 开始，重读既有REC
四文件及定理2.3式(2.8)。来源仍为已登记PR41 / `b4c14823d9a97a45770ed42379673d39b5295be6`，
没有新接收paper，也不推进proof分支扫描水位。脚手架将单对等待标为REC-L6、联合并集界
标为REC-L7；本批准确登记为REC-L7尾界部分。

`F3JointWaitingHaar.lean` 的14条候选声明以真实原配置和真实无限单位Haar流为对象，
定义实际规范对最大等待与实际最大根距、证明逐点矩阵恢复等价，并导出choose-two指数尾界。
[精确映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30rec-l7-实际全矩阵停止尾界候选)
与 [任务](f3_formalization_tasks.md#2026-09-30rec-l7-实际联合停止尾界候选) 双向链接。
源码与有限检查通过不表示形式化完成；未运行本地Lean，待父任务精确Actions。
PAPER-AUDITED状态不变；对数均值、移动模型、素数传递及其它REC开放节点继续保留。

## 2026-09-30 10:12 UTC：REC-L7 实际联合停止尾界已通过精确 CI

代码0324861a6b94294421d692203e8847802b1044f4，树dbbe7e42a1c38aff722b05568ca5c9a957fe69dd，
[push36700614557](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700614557)和
[PR36700618251](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700618251)
均完整成功。14条新声明逐条仅依赖propext、Classical.choice、Quot.sound；全726项
公理输出（725项目+1必需产生器）、109项目源文件、650依赖模块及固定版本、完整构建、
内核回归、覆盖和144240有限检查通过。

已验范围是REC-L7/定理2.3式(2.8)的尾界部分：固定原配置的真实一基最大等待时间，
按i<j恰计choose(m,2)对，K为这些实际有限根距的最大值；逐点证明τ≤T等价于原证书
矩阵恢复全部真实根距，保留∞对角线、命中根和T=0。真实单位Haar无限流的尾概率
不超过min(1,choose(m,2)·exp(-T·3^-K))，仅使用对之间并集界，不假设根对独立。

首轮编译失败已作四处语法/推断/存在量词归一化修复，14条公开命题及模型前提不变。
185653个有限批次（含27607个命中根批次）只是补充语义回归。对数期望界、移动配置、
完整有符号差律及素数传递仍开放，不把尾界当作这些结论。本次状态文档头还需独立完整CI。

## 2026-09-30：REC-L7 实际最大等待期望候选

在已验联合尾界主线ee288806上新增F3JointWaitingMean.lean的12条候选声明。
直接积分已有真实ENat最大等待时间，保留从不命中的∞；逐点尾计数、可测性和非负积分
交换后，用已验实际尾概率控制期望。解析部分调用锁定库的递减函数积分判别、指数
可积性及不定区间积分，将min(1,B exp(-px))在log(B)/p处分割并分别上界，得到
原纸面精确上界1+3^K(1+log choose(m,2))；不是替换成较弱常数或预设几何分布。
进一步候选推出最大等待几乎处处有限，以及原证书矩阵几乎处处最终恢复。

固定原配置C的全部正基深度、m≥2、互异同模3单位根前提保留，K仍为实际有限根距最大值。
本候选尚未编译：源码110文件、737项目声明+1产生器覆盖及6项审计规则测试通过；
294个浮点解析前缀与已有有限根样本尾和只作回归，不能当无限概率/内核证明。
精确Actions构建、公理、回归、覆盖及独立复核仍为接受门禁。移动配置、有符号差律、
素数传递及其余接收任务继续开放；本轮没有新增纸面来源或修改原始研究水位。

## 2026-09-30 10:47 UTC：REC-L7 实际联合等待对数期望已通过精确 CI

代码1b9a0d63b4c2be6d063dda68a60f1ceffa7cf130，树de59e407b238b301cafa9474a4babeb9cb553d58，
[push36704236926](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704236926)与
[PR36704245738](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704245738)
完整成功。12条新声明仅标准公理；全738项公理输出（737项目+1产生器）、110项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查全部通过。

REC-L7/定理2.3式(2.8)的实际最大等待时间满足原精确上界
Eτ≤1+3^K(1+log choose(m,2))，这里期望是保留∞的真实非负积分，K为实际根距最大值。
已证明真实最大等待几乎处处有限，原有证书矩阵几乎处处在某个有限T恢复全部真实距离。
证明调用锁定库的指数积分/积分判别和已验真实联合尾界；没有预设分布或根对独立性。

首轮编译的默认有限区间质量、反单调限制集参数、Nat索引/局部常量展开及符号归一化
已显式修复，12个公开命题及全部前提保持不变。294个浮点解析前缀与28个有限样本尾和
仅为补充回归。显式置信参数δ推论、移动配置、完整有符号差律和素数传递仍开放。
本次状态文档头保留全部已验代码和审计，仍独立执行完整CI。原纸面来源水位不变。

## 2026-09-30：REC 显式置信参数的实际矩阵恢复候选

在已验联合等待尾界/期望主线3b0d3aad上新增F3RecoveryConfidence.lean三条候选声明。
对原固定配置、0<δ<1及自然T满足T≥3^K log(choose(m,2)/δ)，将已验真实尾界反解为
实际失败概率≤δ，再通过已证明的矩阵恢复等价和可测补事件得到实际完整矩阵恢复
概率≥1−δ。K仍为真实有限根距最大值，不把成功事件定义为希望成立的概率结论。

源码111文件、740项目声明+1产生器覆盖与6项审计规则测试通过，但三条声明尚未编译。
36个数值阈值与既有有限根模型的精确有理成功概率仅作回归；精确Actions全部门禁和
独立数学复核仍待执行。此候选不涵盖移动配置、全素数传递、有符号差律或整个REC包；
原纸面来源及研究水位不变。

## 2026-09-30 11:04 UTC：实际完整矩阵置信保证已通过精确 CI

代码361cdd3c958897b342297dfbc7abb55a66e3a4cb，树6979590446d56975243dd667081e37c40542456f，
[push36705872257](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705872257)和
[PR36705919682](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705919682)
首轮完整成功。三条新声明仅标准公理；全741项公理输出（740项目+1产生器）、111项目
源文件、650依赖模块及版本锁、构建、内核回归、覆盖和144240有限检查全部通过。

对原固定配置、0<δ<1和自然T≥3^K log(choose(m,2)/δ)，真实单位Haar流前T次观测使
原证书矩阵恢复全部真实距离的概率至少1−δ。成功事件通过已有逐点矩阵等价和可测尾
补事件证明，不预设目标概率；K为实际根距最大值，根命中∞及真实∞对角线保留。

与先前已验标量尾律/期望、联合尾界/对数期望一起，覆盖纸面定理2.3在固定原局部模型
中的式(2.7)、式(2.8)及其显式置信推论。整个REC包仍未完成：截断概率、移动配置、
全素数传递、有符号差律、被动下界和三等距根精确停止律等继续开放。36个数值阈值与
8个有限根模型有理成功概率仅为回归。独立数学/源码复核通过；此状态文档头仍另行
执行完整CI。原始proof来源水位保持不变。

## 2026-09-30：REC-L12 单次截断证书真实 Haar 概率候选

新增F3TruncatedCertificateHaar.lean十二条候选声明，针对定理2.6式(2.13)：既有
不等或联合饱和证书的真实事件在L<H时等于原深度不等事件，在L≥H时等于共同H球。
因此复用已验单位Haar律给出3^(−L)或1/(2·3^(H−1))，并由实际事件包含得到统一下界。
原固定配置包装使用实际有限正根距，H截断的是R而非b+R；原始命中根的∞保留到截断。

候选尚未编译：源码112文件、752项目声明+1产生器覆盖及六项审计规则测试通过。
30个精确有限剩余类案例包含H=1、L=H和根命中，只是补充回归。H=0被公式明确排除；
该点实际成功率1而误用公式得1/2，体现正精度前提必要。有限批次截断矩阵失败界式(2.14)、
移动配置、素数传递和其他REC节点仍开放。11:09刷新172个实际远端分支，155原水位记录
仅master变化，原研究头未变；近期issues/PR仅本轮工程记录，没有新增外部证明包。
原始来源水位不更新；完整精确Actions门禁及独立复核仍待执行。

## 2026-09-30 11:23 UTC：单次截断证书 Haar 分段律已通过精确 CI

代码94bc0693b5c1bfca7d054d20daf9efea00a0b67a，树9ba2bea3889e77d85a63fcf3c86d3f27b51d0250，
[push36707863669](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707863669)与
[PR36707908267](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707908267)
首轮完整成功。12条新声明仅标准公理；全753项公理输出（752项目+1产生器）、112项目
源文件、650依赖模块及版本锁、构建、内核回归、精确覆盖和144240有限检查通过。

已覆盖REC-L12/定理2.6式(2.13)的实际单次概率：L<H时证书事件等于原不等深度事件，
质量3^(−L)；L≥H时等于真实共同H球，质量1/(2·3^(H−1))，包括L=H。另有可测性、
实际事件包含给出的统一下界、原固定配置包装。H截断标准化R，命中根∞保留至截断，
恢复目标仍为min(L,H)。高距离一般引理允许更广根域，但最终包装保持原C全部前提。

30个精确有限剩余类案例6564次观测含60次根命中只是补充回归；H=0反例说明为何质量
公式要求H≥1。独立源码/数学复核通过。式(2.14)的有限批次截断矩阵尾界、移动配置、
全素数传递与整个REC包仍开放。此状态文档头不变更已验代码或审计，仍单独执行完整CI。

## 2026-09-30：REC-L12 实际有限批次截断矩阵概率候选

新增F3TruncatedBatchHaar.lean十一条候选声明，针对定理2.6式(2.14)。观测参数是
真实有限单位Haar乘积，单次同一参数作用于全部根。每对失败事件等于真实单次成功
补事件的时间乘积矩形；用已验统一成功率下界得到指数尾。已有截断矩阵算法失败
逐点等于规范i<j对失败的并集，系数恰为choose(m,2)，不假设根对独立。目标始终为
min(L,H)，对角线H，保留根命中原深度∞、联合饱和和空批次T=0。

候选尚未编译：源码113文件、763项目声明+1产生器覆盖及六项审计规则测试通过。
84个有限剩余类批次案例只作回归，包含真实矩阵、时间乘积、强相关根对和T=0；
不能代替精确Actions内核/公理/源码/覆盖门禁。移动配置、全素数采样与其他REC节点
仍开放；本轮沿用已接收纸面证明和既有来源水位。

## 2026-09-30 11:47 UTC：实际有限批次截断矩阵尾界已通过精确 CI

代码95c32fe0de79502fba19972d86d327c32103eaf6，树647521f257918a7625542896e07ef320a7dae25f，
[push36710285308](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710285308)与
[PR36710327735](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710327735)
首轮完整成功。11条新声明仅标准公理（证书对称引理不依赖任何公理）；764项总输出
（763项目+1产生器）、113项目源文件、650依赖模块及版本锁、构建、内核回归、一对一
覆盖和144240有限检查通过。测试PR合并树与上述源码头的文件树相同。

已覆盖REC-L12/定理2.6式(2.14)：真实有限单位Haar乘积采样下，既有截断矩阵算法
未恢复min(L,H)的概率≤min(1,choose(m,2)·exp(−T/(2·3^(H−1))))。对角线H、联合饱和、
命中根原深度∞和T=0保留；时间乘积与根对并集分别证明，没有根对独立性假设。
连同已验单次式(2.13)，当前覆盖原固定模型的两条截断概率公式及实际算法事件。

84个有限案例45143批次（含16636根命中批次）只是补充回归。独立数学/源码复核
通过；有限精度不可辨识的完整分布声明、移动配置和全素数传递仍开放，不能把整个
定理2.6或REC包全部标成完成。此状态文档头不变更已验代码/审计，仍另行完整CI。

## 2026-09-30：有限精度双输出完整分布不可辨识候选

新增F3TruncatedNonidentifiability.lean十四条候选声明。先由既有真实尾律、非负性和
根单点零测，使用锁定库的半直线测度唯一性识别完整原深度推前分布；显式证明标准
WithTop整数Borel可测性，保留根命中的∞，不利用非可测map默认分支。再通过可测min
截断和对角映射，证明两根距离均≥H时完整双输出分布相同；真实有限乘积推前接口
给出每个自然T（含0）的完整观测序列分布相同，不只是矩或个别概率相同。

原模型包装保留共同已知基础深度、各自正基深度、m=2、互异同模3单位根及H≥1；
显式比较真实距离H与更高K>H。只针对观测本身，不能解读为给出系数后也无法计算根距，
也不声称有限素数盒中的采样律完全相同。

候选尚未编译：源码114文件、777项目声明+1产生器覆盖及六项审计规则测试通过。
16个有限完整序列直方图案例及3个低于H的反向对照仅作回归。精确Actions全部门禁和
独立复核仍待执行；移动/素数采样、分歧律、被动下界、三等距根及其他任务继续开放。

## 2026-09-30 12:34 UTC：完整双输出截断观测分布已通过精确 CI

代码add478972bb5b3cd2a255cc0aab1ef6e078578b1，树7b38ee3b132fb3039518f4700ea3b4d509cdc44f，
[PR36715105909](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36715105909)
首轮完整成功；实际测试合并提交864ceb48a06109125d76756a0f41bd4161423530的文件树相同。
14条新增声明只有标准公理，778项总审计输出（777项目+1产生器）、114项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查均通过。

现已覆盖REC定理2.6的固定双根、有限精度完整观测分布不可辨识结论：标准单位Haar
采样下，两模型的真实根距均至少H时，每个有限T的完整双输出观测序列具有相同分布，
包括真实距离H与K>H的比较。原模型包装保留共同已知基深度、m=2、互异同模3单位根、
正基深和H≥1；根命中保留原深度∞，明确证明完整可测推前律，不使用非可测map默认值。

该结论仅针对观测接口，不是已知系数后的计算下界，也不是有限素数盒的分布相等。
16个完整序列直方图案例333768输入批次与3个反向控制仅为补充回归。独立数学/源码
复核通过；移动配置、素数传递、完整有符号分歧律、被动样本下界、三等距根停止律及
其他REC节点仍开放，整个包formalization_complete仍为false。此文档头不改已验Lean
代码、Audit或依赖，发布后仍需完整精确头CI和当前主分支检查。

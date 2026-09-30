# F3-REC：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：LEAN-IN-PROGRESS（确定性矩阵及本页所列实际 Haar 单次概率已通过精确 CI；等待律等其余部分未完成）。

## 推荐模块

- \`OmegaBalance/F3DepthCertificate.lean\`
- \`OmegaBalance/F3DepthSampling.lean\`
- \`OmegaBalance/F3DepthTruncation.lean\`

## 目标接口

| 节点 | Lean 名称草案 |
|---|---|
| 不等深度精确根距 | \`rootDepth_min_eq_distance_of_ne\` |
| 单次证书正确性 | \`depthCertificate_sound\` |
| 多证书一致性 | \`depthCertificate_consistent\` |
| 截断证书正确性 | \`truncatedDepthCertificate_sound\` |
| 三等距根有限模型 | \`equidistantThreeRoots_certificate_state\` |

## 形式化顺序

优先形式化确定性部分：
1. ultrametric valuation lemma；
2. 不等观测证书；
3. 截断证书；
4. 根簇树恢复。

概率层先在实际单位 Haar 的有限乘积中证明批次失败律，再另行定义无限流等待时间；不能用直接规定所需质量的几何分布模型替代真实采样证明。真实全素数采样部分依赖外部固定精度分布，不应添加自定义 axiom。

## 边界

本包和 F3-MOM 的矩恢复互补：REC 的精确证书正确性不需要任何无界矩或一致尾界。

## 2026-09-30 确定性实现候选

新增 `OmegaBalance/F3RootCertificates.lean`，实现 REC-L1/L2、单对REC-L4、REC-L11：真实 ℚ_[3] 根，WithTop ℤ 深度，命中根时为∞；不等观测给出精确根距，联合饱和给出截断根距，Option 证书及固定根距下多次证书一致性。12条定理全部登记Audit，代码70becdbf已通过完整门禁。

`F3SharedRootConfig`显式保留b≥1、m≥2、单位根、互异根及同模3球；`f3SharedRootDepth`透明定义为b+v3(d−α_i)。一般超度量适配器有更强的任意三进点定义域，不以总化自然数v3(0)=0替换∞。当前不证明这些抽象根由整数素数乘积产生，不证明采样律、等待时间、矩阵恢复、根簇树或全素数传递，不能把全部REC-1/2/4标为完成。

[持续任务](../../../f3_formalization_tasks.md) · [复用证据](../../../f3_external_reuse.md) · [接收账本](../../../f3_proof_intake.md)。

## 已执行的局部门禁

代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b` 的 [push Lean run 36662676882](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36662676882) 和 [PR Lean run 36662680539](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36662680539) 均通过：620条声明仅标准公理、96源文件、一对一覆盖、三组内核回归与144240有限检查。独立专项复核确认p-adic零点∞、等值未饱和未知、两类有效证书及模型前提非真空。仅升级上述确定性局部节点；REC完整概率/采样主结论仍未完成。此后的文档head再次执行完整CI。


## 2026-09-30 REC-L5 有限矩阵与根簇（已通过精确 CI）

基线 master `5a622dc4e90db25dbc21f926de873be17372ed39`；数学来源为本包
[命题 2.2](proof.md#命题-22无误判的证书算法) 与 REC-L5。
新增 [F3RootReconstruction.lean](../../../../OmegaBalance/F3RootReconstruction.lean)，
直接复用上述已核验单对证书，不重做 REC-L1/L2/L4/L11。

| 精确 Lean 声明 | 来源节点与覆盖 |
|---|---|
| `depthCertificateScan_first` | REC-L4/L5：首个不等观测的前缀、观测本身与精确最小值；前缀长度给出零基观测编号 |
| `depthCertificateScan_eq_none_iff` | REC-L5：未知恰等价于所有已记录深度相等，不能推出根重合或更深 |
| `depthCertificateScan_sound` | REC-L5：允许根随配置移动；显式假设真实根间距离保持固定，推出输出正确 |
| `depthCertificateScan_recover_iff` | REC-L5：单对恢复恰等价于有限数据中存在不等观测 |
| `depthCertificateMatrix_recover` | REC-L5：每个非对角指标对有证书即恢复完整带标签矩阵，对角由实际 `v₃(0)=∞` 校验 |
| `rootDistance_threshold_equivalence` | REC-L5：实际三进根的 `t≤v₃(αᵢ−αⱼ)` 自反、对称、传递 |
| `rootClusterSetoid_refines` | REC-L5：更高阈值的分区细化更低阈值的分区 |
| `depthCertificateMatrix_cluster_iff` | REC-L5：恢复矩阵的阈值测试等价于真实根簇关系 |
| `depthCertificateMatrix_cluster_equivalence` | REC-L5：观测矩阵诱导的阈值关系确为等价关系 |
| `f3SharedRootConfig_matrix_recover` | REC-L5 纸面定义域：公共正基础深度（显式 _hbase）、至少两根、互异同模 3 单位根、单位样本；非对角根距有限 |

算法仅接收有限观测编号列表及其带标签超额深度 `R`，不接收根或真实距离矩阵。
扫描返回距离值；首个观测及其编号由 `depthCertificateScan_first` 的存在性前缀见证，
当前没有把观测编号作为返回数据字段，也未形式化运行时间界。
`hfixed` 比较每个配置的真实 p-adic 根距与参考配置的真实根距，是纸面固定模型假设；
没有把扫描算法的恢复结论或同名目标作为前提。`hcomplete` 仅要求每个非对角指标对
出现不等观测，不要求对角成功，也不保证任何随机采样过程最终产生这些观测。
样本命中根保留 `⊤`，没有使用自然数总化零赋值。

本候选只把根簇树表达为所有阈值下的嵌套 `Setoid` 分区，尚无独立组合树数据结构，
也未形式化由距离矩阵计算全部精确联合深度概率。REC-L3、L6–L10、L12–L13、
截断矩阵扫描、整数素数乘积的根构造及固定精度素数传递继续开放。
全部 10 条 theorem 已一对一登记 Audit；本地源码守卫（97 文件）和覆盖检查（630/630）通过。
代码 `c2fe3c433d69d6d1ef3fd8fd371fca08c8db184d` 的 [push run 36667493101](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36667493101) 与 [PR run 36667536541](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36667536541) 均已完整成功：实际构建、内核回归、630条标准公理声明、97文件源码守卫、一对一覆盖、144240有限检查。仅本节10条确定性声明登记为已核验；完整REC主结果仍未完成。最终文档头另跑全门禁。

[持续任务与范围](../../../f3_formalization_tasks.md#2026-09-30rec-l5-有限矩阵与阈值根簇候选)
· [外部复用门](../../../f3_external_reuse.md#2026-09-30rec-l5-目标优先查重复用)

底层矩阵算法的输入是超额深度R，不处理从原始D估计未知b；纸面模型wrapper显式通过 `_hbase` 保留所有观测配置与参考配置的公共baseDepth，另保留单位样本等前提。

## 2026-09-30 REC-L11 / 截断 REC-L5 有限矩阵（已通过精确 CI）

新增 [F3RootTruncatedReconstruction.lean](../../../../OmegaBalance/F3RootTruncatedReconstruction.lean)。
本轮恢复基于已合入 PR #49 的 master `f50d23667628c868610c34d5157fe9bbd21357d3`，
保留上一节已验完整精度矩阵、公共基础深度 `_hbase` 与精确 CI 的记录。
云工作区更换前的本地候选 `e0d7f9c890031f72e965907e56bdebca868bf557` 已丢失；
本次从保留的原始写入记录恢复 244 行 Lean 源码，Git blob
`4a24db55453664e08976cd883757912c874f1adb` 与更换前记录完全一致。
这确认源码字节恢复，不表示旧提交、工作区或验证结果存续；本次文档在当前主线上增量接回。
数学来源仍为 PR #41 的 `b4c14823d9a97a45770ed42379673d39b5295be6`、proof blob
`ef55306b0c00adc68cfd8407440a4bdd46e6de10`，具体对应定理 2.6 的确定性部分及
命题 2.2 的逐对扫描/阈值根簇方法。这里没有接收新的概率结论，也没有修改原纸面结论。

| 精确 Lean 声明 | 来源节点与覆盖 |
|---|---|
| `truncatedDepthCertificate_eq_some_iff` | REC-L11：证书成功 iff 观测不等或联合饱和，并且输出等于观测最小值 |
| `truncatedDepthCertificate_eq_none_iff` | REC-L11：未知 iff 观测相等且不等于 H；对实际截断数据即相等且小于 H |
| `truncatedDepthCertificateScan_first` | 截断 REC-L5：首个有效观测、输出与所有先前相等未饱和观测；前缀长度给出零基编号 |
| `truncatedDepthCertificateScan_eq_none_iff` | 截断 REC-L5：有限列表未知 iff 每个观测都相等未饱和 |
| `truncatedDepthCertificateScan_sound` | REC-L11 → 截断 REC-L5：移动的真实三进根保持固定距离时，输出必为 min(L,H) |
| `truncatedDepthCertificateScan_recover_iff` | 截断 REC-L5：单对恢复 iff 数据中有不等或联合饱和见证 |
| `truncatedDepthCertificateMatrix_recover_iff` | 截断 REC-L5：完整带标签矩阵恢复 iff 每个非对角指标对有上述见证；已知对角为 H |
| `truncatedRootDistance_threshold_iff` | 截断 REC-L5：t≤H 时，截断矩阵的阈值测试 iff 真实根距测试，包括 t=H |
| `truncatedDepthCertificateMatrix_cluster_iff` | 截断 REC-L5：恢复矩阵在 t≤H 的根簇测试与既有 `rootClusterSetoid` 完全相同 |
| `truncatedDepthCertificateMatrix_cluster_equivalence` | 截断 REC-L5：这些观测矩阵关系自反、对称、传递；复用既有真实根距等价关系 |
| `f3SharedRootConfig_truncatedMatrix_recover_iff` | REC-L11 / 截断 REC-L5 原纸面定义域：H≥1、公共正基础深度（显式 `_hbase`）、至少两根、互异同模 3 单位根及单位样本下的恢复 iff |

算法仅接收 H、有限观测编号列表与已经截断的带标签数据 Y，不接收根或目标矩阵。
`truncatedDepthWitness` 透明定义为 `y ≠ z ∨ (y = H ∧ z = H)`；不能丢弃联合饱和的
等值观测。目标透明定义为 `truncatedRootDistance = min(rootDistance,H)`，对角严格为
`min(∞,H)=H`；不能把它改回 ∞ 或把 H 以上真实根距视为已恢复。
一般适配器允许任意实际 `ℚ_[3]` 点；纸面 wrapper 显式保留完整
`F3SharedRootConfig`、H≥1、样本为单位及公共正基础深度 `_hbase`。固定距离前提比较实际三进
根距，完整性条件仅要求有限数据的可观察见证，均不预设待证算法输出。

所有根簇结论都有 t≤H；它们复用已有嵌套 `Setoid`，因此既有
`rootClusterSetoid_refines` 继续给出精度范围内的层级细化。本文件不重建组合树、
不证明恢复 H 以上信息、局部采样律、REC-L12 的概率等待界、整数素数乘积根构造或
固定精度全素数传递。全部 REC 概率主结果仍未完成。

11 条新增定理全部一对一加入 Audit；恢复后重新执行本地源码守卫 98 文件、覆盖
641/641、`git diff --check`，均通过。重新执行的有限 sanity check 涉及 178746 个整数根
观测、180 组有限矩阵与 365 个已恢复阈值分区，包括空列表、命中根、相等未饱和、
联合饱和、移动根及阈值 H。有限检查及源码恢复不等于内核证明；按任务约定没有执行
本地 Lean/Lake。随后本批代码 `564bb4987980002f37990c2346a847f47138095e` 的 [push run36671721342](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36671721342) 与 [PR run36671762437](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36671762437) 均完整通过：641条仅标准公理、98源文件无逃逸、一对一覆盖、内核回归与144240有限检查。仅本节11条确定性声明登记已核验；最终文档头另验全门禁。

[持续任务](../../../f3_formalization_tasks.md#2026-09-30rec-l11--截断-rec-l5-有限矩阵候选)
· [外部复用证据](../../../f3_external_reuse.md#2026-09-30rec-l11--截断-rec-l5-增量复用门)
· [来源接收与实现区分](../../../f3_proof_intake.md#2026-09-30rec-有限精度实现增量)

输入阈值H作用于已减去已知公共基础深度b的超额深度R，即Y=min(R,H)。它不是对原始D在同一H处截断的接口；不会把这两种观测混用。

## 2026-09-30 REC-L3 actual Haar probability candidate

Baseline master `8548f385e095bf399c27bc3388f8128e4c7fc93c`.
`PadicIntHaar.lean` minimally ports five individually auditable CC0 declarations;
`F3UnitHaar.lean` constructs concrete normalized additive Haar, proves actual
unit-domain mass 2/3 and normalizes its restriction; `F3RootDepthHaar.lean`
connects the existing actual `ℚ_[3]` / `WithTop ℤ` rootDepth to residue fibers and
proves the positive unit-root tail `1/(2*3^(t-1))`. A sample at the root retains
infinite depth, and the residue theorem includes it without totalized valuation.
This candidate covers the normalization and single-root tail input to REC-L3.
Exact layers, unequal-depth mass, root-nullity, full signed difference law,
configuration wrappers, independent waiting and prime transfer remain open at
this checkpoint. No sampling-law premise, geometric PMF declaration or count
assumption replaces a proof. Source/API reuse and licensing are recorded in
[the reuse ledger](../../../f3_external_reuse.md#2026-09-30-rec-l3-actual-haar-law-target-first-reuse-gate).
All declarations are registered once in Audit. Local source/coverage checks are
not Lean execution; exact locked-pin CI remains required before status promotion.

### Extension of the actual Haar candidate

`F3RootDepthLaw.lean` adds eight declarations: finite-layer set difference and
measurability, exact positive layer mass 3^-t, zero layer mass 1/2, the integer
strict-threshold adapter, unequal-depth event as two next-level balls, their
disjointness, and actual unequal-depth probability 3^-L for genuine unit roots
with finite L≥1. This establishes candidate coverage of the single-observation
probability (2.3), without taking the requested law as an assumption.

`F3SharedRootHaar.lean` adds six declarations: original model roots have norm 1,
mkUnits preserves the exact ℚ_[3] root and gives real units, and the original
F3SharedRootConfig receives tail/layer/unequal-event wrappers. Positive base depth,
cardinality ≥ 2, distinct unit roots and common first residue remain in the same
configuration structure; observations are excess depths R, not raw D.

`F3RootDepthNull.lean` adds three declarations: ambient Haar singletons have
mass 0 by containment in all residue fibers, normalized unit Haar singletons also
have mass 0, and the infinite-depth event is exactly a null root point. The proof
uses locked ENNReal.exists_inv_two_pow_lt and pow_le_pow_left', not a new
non-atomicity hypothesis. The full signed integer difference law still needs an
explicit almost-everywhere finite-difference interface and is not claimed here.

All17 extension declarations are in Audit. These are source candidates awaiting
actual Lean CI; local source/coverage/finite checks do not promote them. Independent
waiting time, expected stopping time, complete joint law and prime transfer remain
open. The first checkpoint's actual CI36675740452 failed on import/namespace/cast
elaboration; the 5 ported Haar declarations compiled. Those concrete errors are
fixed in the subsequent candidate, without changing pinned dependencies.

## 2026-09-30：REC-L3 实际 Haar 单次概率已通过精确 CI

代码 `dc0632322c3de631a167f6cb7308d01e7b0069fc` 的
[push 36681283200](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36681283200) 与
[PR 36681288176](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36681288176)
全部成功：679 条仅含标准 Lean 公理，104 源文件无逃逸，679/679 一对一覆盖，
完整构建、三组内核回归、144240 有限检查及11项边界测试通过。以下38条新增声明
仅升级其实际覆盖的单次 Haar 概率范围；上文 candidate / pending 描述为此前检查点历史。
本节文档后的最终提交仍单独验证。

| 模块与纸面依赖 | 精确已验声明（均为 OmegaBalance 命名空间） |
|---|---|
| `PadicIntHaar.lean`：CC0 最小纤维测度复用闭包 | `padicInt_fiber_translate`, `padicInt_measurable_zero_fiber`, `padicInt_measurable_fiber`, `padicInt_haar_fiber_eq_zero_fiber`, `padicInt_haar_fiber` |
| `F3UnitHaar.lean`：实际单位域和归一化，不假设球质量 | `f3PadicHaar_univ`, `f3PadicInt_not_isUnit_iff`, `f3PadicUnitSet_compl`, `f3PadicUnitSet_measurable`, `f3PadicHaar_units`, `f3UnitHaar_univ`, `f3UnitHaar_units`, `f3UnitHaar_nonunits`, `f3PadicInt_unit_fiber_subset`, `f3UnitHaar_fiber` |
| `F3RootDepthHaar.lean`：REC-L3 单根尾律及无限根点的同余桥 | `rootDepth_ge_iff_toZModPow`, `f3RootDepthTail_eq_fiber`, `f3RootDepthTail_measurable`, `f3RootDepthTail_zero`, `f3RootDepthTail_antitone`, `f3UnitHaar_rootDepth_ge` |
| `F3RootDepthLaw.lean`：REC-L3 正层、零层、式(2.3)单次不等证书概率 | `f3RootDepthLayer_eq_sdiff`, `f3RootDepthLayer_measurable`, `f3UnitHaar_rootDepth_eq`, `f3UnitHaar_rootDepth_zero`, `rootDepth_nat_lt_iff`, `rootDepth_ne_iff_mem_tail_union`, `f3RootDepthTail_disjoint`, `f3UnitHaar_rootDepth_ne` |
| `F3SharedRootHaar.lean`：原 F3SharedRootConfig 域保持包装 | `f3SharedRootConfig_root_norm`, `f3SharedRootUnit_coe`, `f3SharedRootUnit_isUnit`, `f3SharedRootConfig_unitHaar_depth_ge`, `f3SharedRootConfig_unitHaar_depth_eq`, `f3SharedRootConfig_unitHaar_depth_ne` |
| `F3RootDepthNull.lean`：根命中事件零测，不将∞总化为0 | `f3PadicHaar_singleton`, `f3UnitHaar_singleton`, `f3UnitHaar_rootDepth_top` |

精确概率是实际单位 Haar 下的 Pr(R≥t)=1/(2·3^(t−1))（t≥1）、
Pr(R=t)=3^(-t)（t≥1）、Pr(R=0)=1/2，以及具有有限真实根距 L≥1 的
Pr(R_i≠R_j)=3^(-L)。共享根包装保留公共正 b、m≥2、互异单位根和同模3前提，
观测为 R，未将 D=b+R 与 R 混用。根点是证明出的零测例外，未添加非原子性假设。

剩余：完整有符号整数差的几乎处处定义和分布、独立整组采样的几何等待律及均值、
多对联合概率/恢复界、被动下界、整数素数乘积根构造、固定精度全素数传递。
本批不把随机变量定义成几何 PMF 后宣告等待律，也不假设各根坐标相互独立。
[任务账本](../../../f3_formalization_tasks.md) · [复用与许可](../../../f3_external_reuse.md)


## 2026-09-30 REC-L6 fixed-root finite-batch candidate

Baseline master `0bd5333e92b429306ffb139728c04cd4a1ee796b` (684 project
declarations plus the required external RUN producer). The accepted source is
proof theorem 2.3, equation (2.7), with its input theorem 2.1 / equation (2.3)
and deterministic Proposition 2.2. The existing four-file REC package was read
in full. No new mathematical source or new source watermark is introduced.

New module [F3RootBatchHaar.lean](../../../../OmegaBalance/F3RootBatchHaar.lean)
uses the genuine finite product `Measure.pi (fun _ : Fin T => f3UnitHaar)`.
The coordinate `d t` is shared by all root labels in observation t. The roots
are fixed across this batch. Their distance is the actual `rootDistance`,
equal to a finite natural L≥1; root-hit depth remains `⊤` in `WithTop ℤ`.
The equal-event mass is derived from the proved single-observation unequal
mass. Product factorization uses the locked `Measure.pi_pi`; no probability
formula or independence among labels is assumed.

| Exact declaration in namespace OmegaBalance | Scope |
|---|---|
| `f3RootDepth_ne_measurable` | Unequal event is the measurable union of the actual next-level root balls |
| `f3RootDepth_equal_measurable` | Equal event is the measurable complement |
| `f3UnitHaar_rootDepth_equal` | Actual unit Haar equal-event probability `1 - 3^(-L)` |
| `f3RootDepthBatchFailure_eq_pi` | Transparent all-equal batch event is the product rectangle |
| `f3RootDepthBatchFailure_zero` | Empty batch failure event is all of the empty sample space |
| `f3RootDepthBatchFailure_measurable` | Finite product failure event is measurable |
| `f3UnitHaar_batch_failure` | Actual all-T failure probability `(1 - 3^(-L))^T`, including T=0 |
| `depthCertificateScan_finRange_eq_none_iff` | Existing ordered scan is unknown exactly on that failure event |
| `f3UnitHaar_depthCertificateScan_none` | Actual product probability of the existing scan remaining unknown |
| `f3SharedRootConfig_unitHaar_scan_none` | Same statement for one fixed original configuration, preserving its model hypotheses |

The algorithm continues to receive only the time list and labelled excess
depths R. It does not receive roots or target L. The wrapper retains positive
base depth b, m≥2, distinct congruent unit roots through `F3SharedRootConfig`;
it does not confuse R with raw D=b+R. Samples are distributed by the existing
actual unit-supported measure rather than restricted by a fabricated finite
sample-space law. ENNReal subtraction is the usual probability complement,
so the subtraction is justified by a probability measure.

Validation: all 10 declarations have exactly one Audit entry; local source
guard (106 files), coverage (694 project declarations plus 1 external producer),
15 compatibility tests, 6 audit-rule tests and 11 existing boundary tests pass.
A separate exhaustive finite-residue sanity check examined 333738 batches in
24 cases: L=1,2,3; roots 1 or 2 and their translate by 3^L; T=0,1,2,3. It keeps
root hits infinite, verifies the scan returns either unknown or actual L, and
counts the failure fraction exactly. None of these is a kernel check.
`python3 scripts/verify.py` exits 2 because Lake is absent; actual Lean build,
kernel regression and axiom execution remain pending exact-head CI.

This is only the fixed-root finite-batch slice of REC-L6 / (2.7). There is no
infinite one-based waiting random variable, expectation, moving-configuration
sampling generalization, unordered-pair union bound, exponential recovery
bound, or prime-sampling transfer. Those accepted tasks remain open. The
finite batch includes T=0; it is not a definition of a zero-based geometric
waiting variable. [Reuse and pin evidence](../../../f3_external_reuse.md#2026-09-30-rec-l6-finite-batch-target-first-reuse-gate).

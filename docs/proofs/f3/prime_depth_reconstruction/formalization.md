# F3-REC：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：LEAN-IN-PROGRESS（确定性局部引理已通过精确CI，主结果其余部分未完成）。

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

概率等待时间可先在有限几何分布模型中证明；真实全素数采样部分依赖外部固定精度分布，不应添加自定义 axiom。

## 边界

本包和 F3-MOM 的矩恢复互补：REC 的精确证书正确性不需要任何无界矩或一致尾界。

## 2026-09-30 确定性实现候选

新增 `OmegaBalance/F3RootCertificates.lean`，实现 REC-L1/L2、单对REC-L4、REC-L11：真实 ℚ_[3] 根，WithTop ℤ 深度，命中根时为∞；不等观测给出精确根距，联合饱和给出截断根距，Option 证书及固定根距下多次证书一致性。12条定理全部登记Audit，代码70becdbf已通过完整门禁。

`F3SharedRootConfig`显式保留b≥1、m≥2、单位根、互异根及同模3球；`f3SharedRootDepth`透明定义为b+v3(d−α_i)。一般超度量适配器有更强的任意三进点定义域，不以总化自然数v3(0)=0替换∞。当前不证明这些抽象根由整数素数乘积产生，不证明采样律、等待时间、矩阵恢复、根簇树或全素数传递，不能把全部REC-1/2/4标为完成。

[持续任务](../../../f3_formalization_tasks.md) · [复用证据](../../../f3_external_reuse.md) · [接收账本](../../../f3_proof_intake.md)。

## 已执行的局部门禁

代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b` 的 [push Lean run 36662676882](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36662676882) 和 [PR Lean run 36662680539](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36662680539) 均通过：620条声明仅标准公理、96源文件、一对一覆盖、三组内核回归与144240有限检查。独立专项复核确认p-adic零点∞、等值未饱和未知、两类有效证书及模型前提非真空。仅升级上述确定性局部节点；REC完整概率/采样主结论仍未完成。此后的文档head再次执行完整CI。


## 2026-09-30 REC-L5 有限矩阵与根簇候选（尚未执行 Lean）

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
| `f3SharedRootConfig_matrix_recover` | REC-L5 纸面定义域：正的固定基础深度、至少两根、互异同模 3 单位根、单位样本；非对角根距有限 |

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
当前容器无 Lean/Lake，完整内核/回归/公理检查尚未执行；不得用本段升级为 LEAN-PROVED。

[持续任务与范围](../../../f3_formalization_tasks.md#2026-09-30rec-l5-有限矩阵与阈值根簇候选)
· [外部复用门](../../../f3_external_reuse.md#2026-09-30rec-l5-目标优先查重复用)

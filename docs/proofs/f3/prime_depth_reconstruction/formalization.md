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

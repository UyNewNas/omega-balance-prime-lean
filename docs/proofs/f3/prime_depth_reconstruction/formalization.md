# F3-REC：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

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

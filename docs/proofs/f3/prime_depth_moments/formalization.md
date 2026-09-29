# F3-MOM：形式化映射（更新稿）

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3PrimeDepthFinite.lean\`
- \`OmegaBalance/F3PrimeDepthMoments.lean\`
- \`OmegaBalance/F3PrimeDepthGenerating.lean\`

## 可优先形式化

| 节点 | Lean 名称草案 |
|---|---|
| 根深度有限模分布 | \`f3Depth_root_count_mod_pow\` |
| 极深单坐标支撑限制 | \`f3Depth_atMostOne_above_maxRootDistance\` |
| 局部平方差矩 | \`f3Depth_pair_sqDiff_finite\` |
| 根树有限 PGF | \`f3Depth_generatingFunction_finite\` |
| 总深度最终尾律 | \`f3Depth_sum_eventual_geometric_tail\` |

## 外部分析阻塞

全素数侧的：
- 固定形状主项；
- Selberg 上界筛；
- 指数加权极限交换；

目前都不应以自定义公理代替。

F3-MOM-4 的**局部**有理生成函数完全是有限根树/几何级数，可独立先形式化。

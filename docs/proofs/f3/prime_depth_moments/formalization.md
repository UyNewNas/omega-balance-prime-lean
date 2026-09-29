# F3-MOM：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3PrimeDepthLocal.lean\`
- \`OmegaBalance/F3PrimeDepthFinite.lean\`
- \`OmegaBalance/F3PrimeDepthMoments.lean\`

## 可先形式化的有限层

| 节点 | 建议接口 |
|---|---|
| 根深度边缘分布的有限模版本 | \`f3Depth_root_count_mod_pow\` |
| 两根距离导致的平方差有限和 | \`f3Depth_pair_sqDiff_sum\` |
| 均值/二阶矩有限模公式 | \`f3Depth_mean_secondMoment_finite\` |
| 根距离到协方差的有限精度公式 | \`f3Depth_covariance_finite\` |

## 分析阻塞

F3-MOM-1/2 的全素数极限依赖：
- 固定形状素数主项；
- Selberg 上界筛；
- 统一尾界与极限交换。

这些不是当前仓库已有 Lean 分析数论接口。不要通过自定义 axiom 占位。

## 建议顺序

先把局部 Haar 模型全部改写成有限模 \(3^T\) 精确计数并形式化；随后再把极限层标记为外部分析阻塞。F3-MOM-3 中“给定矩收敛后恢复 \(L_{ij}\)”的代数部分可以独立形式化。

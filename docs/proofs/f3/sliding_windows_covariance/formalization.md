# F3-WIN：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3SlidingLocal.lean\`
- \`OmegaBalance/F3SlidingWindows.lean\`
- \`OmegaBalance/F3SlidingCovariance.lean\`

## 目标接口

| 节点 | Lean 名称草案 |
|---|---|
| 容量公式 | \`translatedPair_pairCapacity\` |
| 二点尾有限周期公式 | \`translatedPair_twoPointTail_modPow\` |
| 最佳滑窗第二峰 | \`translatedPair_sliding_secondPeak\` |
| 单峰剔除公式 | \`translatedPair_sliding_removedMax_sum\` |
| 截断协方差 | \`translatedPair_covariance_truncated\` |
| 协方差极限闭式 | \`translatedPair_covariance_formula\` |
| 协方差恢复 d | \`translatedPair_covariance_recovers_step\` |
| n 平移不可辨识 | \`translatedPair_translation_invariant_statistics\` |

## 建议顺序

先完全形式化容量、有限周期尾计数、滑动窗口第二峰和剔除恒等式；这些是纯有限整数/模 \(3^T\) 内容。协方差极限最后通过截断周期函数与有限平均推进。

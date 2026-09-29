# F3-PEAK：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3PeakLocal.lean\`
- \`OmegaBalance/F3PeakFinite.lean\`
- \`OmegaBalance/F3PeakExamples.lean\`

## 建议接口

| 书面节点 | Lean 名称草案 |
|---|---|
| 二次差分分解 | \`translatedPairG_sub_factor\` |
| 双峰整除二分 | \`translatedPair_pair_depth_divisibility\` |
| 双峰普通大小界 | \`translatedPair_pair_depth_bound\` |
| 第二极值有限区间界 | \`translatedPair_second_peak_bounds\` |
| 反射恢复另一根类 | \`translatedPair_reflect_root_class\` |
| 完整 \(3^T\) 区段尾计数 | \`translatedPair_complete_block_tail_count\` |
| 双剔除总和 | \`translatedPair_two_peak_removed_sum\` |
| 整数迹直方图 | \`translatedPair_integer_trace_histogram\` |
| 高孤峰构造 | \`translatedPair_arbitrarily_high_isolated_peak\` |
| 超临界峰递推 | \`translatedPair_supercritical_gap\` |

## 说明

这一包的大部分内容只涉及整数整除、有限剩余类和有限求和，比上一轮最高峰的 \(S\)-部分极限定理更适合 Lean。建议先完全形式化 PEAK-1/2/3 的有限版本，再处理 Hensel 构造。

不需要、也不应为了形式化这些有效结论引入 Bugeaud–Evertse–Győry 为公理。

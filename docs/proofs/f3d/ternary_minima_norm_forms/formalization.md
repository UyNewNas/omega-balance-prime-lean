# F3D-TERN：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3DNormForms.lean\`
- \`OmegaBalance/F3DTernaryMin.lean\`
- \`OmegaBalance/F3DMinDegree.lean\`

## 目标接口

| 节点 | Lean 名称草案 |
|---|---|
| 二元无抵消 \(Q,H\) | \`f3D_binary_normForms\` |
| 三输入一倍九次构造 | \`f3D_ternary_min_degree_le_nine\` |
| 两倍十次构造 | \`f3D_ternary_twiceMin_degree_le_ten\` |
| 分母次数代价 | \`f3D_min_denominator_degree_cost\` |
| 三元二次型非各向异性 | \`ternaryQuadratic_over_F3_has_nontrivial_zero\` |
| 三元范数形式 | \`f3D_ternary_cubic_normForm\` |
| 一般有限域范数提升 | \`f3D_normForm_minVal\` |
| 9–10–9 谱 | \`f3D_ternary_min_degree_spectrum\` |
| 分组范数上界 | \`f3D_min_degree_grouped_norm_bound\` |

## 工程建议

先形式化显式 9/10/9 三个构造和有限域 \(\mathbf F_3\) 引理，再处理一般多变量齐次正规化与下界。一般有限域范数形式可能需要先确认 mathlib 当前有限域扩张/Norm API。

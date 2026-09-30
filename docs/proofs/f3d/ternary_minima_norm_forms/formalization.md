# F3D-TERN：形式化映射

数学状态：PAPER-AUDITED（保留原分项状态；2026-09-30 仅补齐 TERN-6 的 m≥2 边界，不是整体重新审计）。Lean 状态：NOT-STARTED。

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
| 分组范数界（m≥2） | \`f3D_min_degree_grouped_norm_bound\`，必须显式接收 `2 ≤ m` |

TERN-6 的目标是 \(3m\le\mathfrak d_m(1)\le m(\lceil\sqrt m\rceil+1)\)，前提为 \(m\ge2\)。\(m=1\) 用恒等对得到次数上界 1，不能复用下界 3m。齐次正规化（TERN-L5）同样显式保留 m≥2。见 [修正报告](../../../../reports/f3d_proof_boundary_corrections.md)。

## 工程建议

先形式化显式 9/10/9 三个构造和有限域 \(\mathbf F_3\) 引理，再处理一般多变量齐次正规化与下界。一般有限域范数形式可能需要先确认 mathlib 当前有限域扩张/Norm API。

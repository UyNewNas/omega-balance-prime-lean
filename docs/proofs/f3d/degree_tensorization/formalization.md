# F3D-DEG：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3DDegreeLocal.lean\`
- \`OmegaBalance/F3DDegreeTensor.lean\`
- \`OmegaBalance/F3DDegreeExamples.lean\`

## 目标接口

| 节点 | Lean 名称草案 |
|---|---|
| 单输入齐次归约 | \`f3D_homogeneous_degree_reduction\` |
| 尾斜率次数下界 | \`f3D_degree_ge_tailSlope\` |
| \(H_k\) 无抵消 | \`f3D_noCancellation_homogeneousForm\` |
| \(k t_+\) 精确次数 | \`f3D_degree_mul_posPart\` |
| 多输入截面下界 | \`f3D_degree_ge_sum_sectionDegrees\` |
| 有符号和张量化 | \`f3D_degree_signedSum_comp\` |
| min/max 精确次数 | \`f3D_degree_min_max\` |
| 无固定除 \(k\) 器 | \`f3D_no_polynomial_divider\` |
| \(p=2\) 单位层检测 | \`f2D_unitLayer_detector\` |

## 工程难点

最难的是多齐次最低权分量的抽取和“指定 \(F\) 壳层的整数点 Zariski 稠密”辅助引理。建议先独立形式化一个一般的多项式缩放 lemma，再套到 \(P\pm Q\)。

## 依赖

可复用已合入的 F3D-POLY / F3D-MULTI 书面接口，但当前仓库尚无这些结果的 Lean 实现，因此代码层不能直接假设它们为 theorem。形式化时应从底层重新建立所需局部 lemma。

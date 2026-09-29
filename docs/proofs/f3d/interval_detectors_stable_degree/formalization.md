# F3D-STABLE：形式化映射

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

## 推荐模块

- \`OmegaBalance/F3DIntervalDetector.lean\`
- \`OmegaBalance/ProjectiveResidueKernel.lean\`
- \`OmegaBalance/F3DStableDegree.lean\`

## 第一阶段：局部显式构造

优先形式化：
- \(q=1,2\) 的二次阶跃；
- 四次区间检测器；
- 线性平移；
- 具体有限 \(K_r\) 矩阵与投影分解。

建议接口：
- \`f3D_intervalDetector_quartic\`
- \`f3D_intervalDetector_degree_ge_four\`
- \`projectiveResidueKernel\`
- \`projectiveResidueKernel_inverse\`

## 第二阶段：稳定下界

需要：
- 代数闭包上的根分解；
- 射影弦距核；
- 剩余类平均；
- 非负权重剖面；
- \(\ell^1\) 质量下界。

这部分工程明显重于前面的显式区间检测器。

## 第三阶段：构造与极限

形式化有限剩余类核列的二次多项式实现、有理线性方程清分母以及次可加极限。有限集合显式公式可作为稳定主定理之后的代数推论。

## 注意

当前仓库还没有一般的“多项式最小实现次数”Lean 框架。不要用 meta-level degree counting 或自定义 axiom 绕过原整数多项式总次数定义。

# F3D-POLY：形式化映射与阻塞依赖

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

[定理](theorem.md) · [完整证明](proof.md) · [PDF](paper.pdf) · [引理 DAG](scaffolding.md)

## 1. 推荐模块

- OmegaBalance/F3DPolynomialLocal.lean
- OmegaBalance/F3DPolynomialRealization.lean
- OmegaBalance/F3DPolynomialDegree.lean

## 2. 目标接口

| 节点 | 建议 Lean 名称 | 状态 |
|---|---|---|
| 定义域 | F3D.Domain | 未实现 |
| \(F_{3,D}\) | f3D | 先核对现有接口 |
| POLY-L1 | f3D_eq_padicValRat_ratio | 未实现 |
| POLY-L2–L4 | f3D_exactZeroDetector | 未实现 |
| POLY-L5 | f3D_shift | 未实现 |
| F3D-POLY-1 | f3D_exactLayerDetector | 未实现 |
| POLY-L6 | padicVal_poly_pow_eventually_affine | 未实现 |
| POLY-L8 | padicVal_rho_eq_posPart | 未实现 |
| POLY-L9 | eventuallyAffine_eq_hingeSum | 未实现 |
| POLY-L10/L11 | f3D_realize_eventuallyAffine | 未实现 |
| F3D-POLY-2 | f3D_polynomial_realizable_iff_eventuallyAffine | 未实现 |
| POLY-L12 | f3D_homogeneous_reduction | 未实现 |
| F3D-POLY-3 | f3D_minDegree_basic_ops | 未实现 |
| F3D-POLY-4 | f3D_not_realizable_sq 等 | 未实现 |

## 3. 形式化顺序

第一阶段优先完成和差坐标、E0、模 9 精确计算、层平移、rho 与绝对值构造。这些基本不依赖高阶 p-adic 代数。

第二阶段形式化最终仿射函数、离散二阶差分有限支撑及齐次化构造。

第三阶段处理非齐次降阶和四次下界；这一层需要 \(\mathbb Q_3\) 多项式根、不可约性与 Hensel。

## 4. Mathlib 接口

在线 Mathlib 文档当前可见：

- padicValRat.mul
- padicValRat.pow
- padicValRat.zpow
- padicValRat.div
- padicValRat.add_eq_min

以及 Mathlib.NumberTheory.Padics.Hensel。

实际编码前必须在仓库固定 mathlib revision 中重新确认名称与签名，不能直接假定在线 master 与 pin 完全一致。

## 5. 语义约束

1. \(F_{3,D}\) 为整数值差分。
2. 定义域排除 \(n=\pm d\)。
3. 全域实现必须保证输出也始终在定义域。
4. 分类只针对固定整数系数多项式对。
5. 中间有理函数必须最终清分母回到整数多项式。
6. 次数下界允许原候选非齐次，所以必须保留 POLY-L12。
7. 双输入乘法不可能性通过对角代入 \(Y=X\) 推出。

## 6. 验证登记

| 项目 | 状态 |
|---|---|
| 完整书面证明 | 已整理 |
| 书面审计 | 已完成 |
| PDF | workflow 生成 |
| 新增 Lean 声明 | 0 |
| Lean kernel 验证 | 无 |
| 主结果状态 | NOT-STARTED |

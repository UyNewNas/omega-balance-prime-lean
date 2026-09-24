# F₃ 深层推论：形式化覆盖与边界

日期：2026-09-24。本轮将此前 `deeper_corollaries.md` 的局部算术推论整理为 Lean 证明，并补上相关计算的有限基础。**不是全部分析结论均已形式化。** 是否通过内核检查，以对应提交的 Lean CI、公理日志及覆盖检查为准。

## 1. 已有代码的覆盖地图

下列声明均提供证明项，位于 `OmegaBalance` 命名空间；没有将有限验算或外部结论写成公理。

| 原结论 | Lean 接口 | 文件 |
|---|---|---|
| 任意正指数幂的完整层级和符号公式 | `f3_pow_depth`, `f3_pow`, `f3Side_pow` | [F3Powers.lean](../OmegaBalance/F3Powers.lean) |
| 模 3 的幂下，幂等于 1 的精确指数条件 | `f3_pow_zmod_neg_iff`, `f3_pow_zmod_pos_iff` | [F3Order.lean](../OmegaBalance/F3Order.lean) |
| 实际乘法阶塔，不是候选阶的定义 | `f3_orderOf_neg`, `f3_orderOf_pos`, `f3_orderOf` | [F3Order.lean](../OmegaBalance/F3Order.lean) |
| 孪生素数在各层的阶相差恰好二倍 | `f3_twin_orderOf` | [F3Order.lean](../OmegaBalance/F3Order.lean) |
| F₃=1 的原根判据，表为实际阶达到最大值 | `f3_eq_one_iff_order_nine`, `f3_eq_one_iff_maximal_order_tower` | [F3Primitive.lean](../OmegaBalance/F3Primitive.lean) |
| 相反等层输入的和／积二分 | `f3_opposite_sum_product`, `f3_opposite_sum_product_min` | [F3SumProduct.lean](../OmegaBalance/F3SumProduct.lean) |
| 孪生乘积使层级加倍 | `f3_twin_product_of_mod`, `f3_twin_product` | [F3SumProduct.lean](../OmegaBalance/F3SumProduct.lean) |
| 附加乘积条件下的加强间距格点 | `f3_product_refined_gap`, `f3_product_gap_dichotomy` | [F3SumProduct.lean](../OmegaBalance/F3SumProduct.lean) |
| 正规化单位坐标 U 的完全乘法性与深度 | `f3Unit_mul`, `f3Unit_depth` | [F3Coordinates.lean](../OmegaBalance/F3Coordinates.lean) |
| 同层抵消的精确剩余多项式及首次升层判据 | `f3_same_level_cancellation`, `f3_same_level_rises_iff` | [F3Coordinates.lean](../OmegaBalance/F3Coordinates.lean) |
| 不存在仅用两个 F₃ 值计算乘积 F₃ 的通用标量规则，即使输入限定为素数 | `f3_no_scalar_mul_rule` | [F3DeeperExamples.lean](../OmegaBalance/F3DeeperExamples.lean) |
| 有理数延拓及自然数／整数兼容 | `f3Rat_int`, `f3Rat_nat`, `f3Rat_neg` | [F3Rational.lean](../OmegaBalance/F3Rational.lean) |
| Cayley 坐标把星运算变成乘法；F₃ 对星运算严格可加 | `f3Cayley_star`, `f3Rat_star`, `f3Rat_star_of_gt_one` | [F3Rational.lean](../OmegaBalance/F3Rational.lean) |
| 大于 1 的有理数上星运算闭合、交换、结合 | `f3Star_gt_one`, `f3Star_comm`, `f3Star_assoc` | [F3Rational.lean](../OmegaBalance/F3Rational.lean) |
| 有限整除层展开等于截断赋值 | `v3Trunc_eq_min`, `f3Trunc_eq_clipped`, `f3Trunc_eq_f3` | [F3Finite.lean](../OmegaBalance/F3Finite.lean) |
| 截断函数的精确周期与原函数的有限和 | `f3Trunc_periodic`, `f3_sum_range` | [F3Finite.lean](../OmegaBalance/F3Finite.lean) |

## 2. 主要公式和实际前提

令 d=|F₃(n)|。对 n>1、3∤n、e>0：

```math
|F_3(n^e)|=d+v_3(e),\qquad
F_3(n^e)=-(-s(n))^e\,(d+v_3(e)),
```

其中 s(n)=`f3Side n`，在该定义域就是 F₃ 的符号。对 r>0：

```math
\operatorname{ord}_{3^r}(n)=
\begin{cases}
3^{\max(r-d,0)},&n\equiv1\pmod3,\\
2\cdot3^{\max(r-d,0)},&n\equiv2\pmod3.
\end{cases}
```

源码使用真正的 `orderOf (n : ZMod (3 ^ r))`。自然数减法 `r-d` 正好表达 max(r-d,0)。正侧结论保留 r>0，避免把模 1 的退化情况算错；指数公式保留 e≠0。

对 p,q>1、k>0、F₃(p)=k、F₃(q)=-k：

```math
\big(v_3(p+q)=k<v_3(pq+1)\big)
\quad\text{或}\quad
\big(v_3(pq+1)=k<v_3(p+q)\big).
```

如果进一步 p<q、两者为奇数，并且 **额外**满足 F₃(pq)=2k，则

```math
q=p+2+2\cdot3^{2k}r,\qquad r\in\mathbb N.
```

没有任何素数对存在性隐藏在这些假设里。孪生素数使附加乘积条件成立，但其逆不成立；(17,181) 是精确门槛上的反例，已有 Lean 回归证明。

正规化坐标定义为 U(n)=-s(n)n。对于 m,n>1、3∤mn：

```math
U(mn)=U(m)U(n),\qquad v_3(U(n)-1)=|F_3(n)|.
```

若 U(m)=1+3ᵏa、U(n)=1+3ᵏb，则

```math
|F_3(mn)|=k+v_3(a+b+3^kab).
```

该公式只需坐标等式，不需假装它们已经表达精确层级；在两输入恰好同层时，a,b 进一步是 3-进单位。对 k>0，输出高于 k 当且仅当 3∣a+b。`f3Unit` 是一个整数坐标，**不是三进对数的替代定义**。

有理数上记 T(x)=(x+1)/(x-1)，x⋆y=(xy+1)/(x+y)：

```math
T(x\star y)=T(x)T(y),\qquad F_{3,\mathbb Q}(x\star y)=F_{3,\mathbb Q}(x)+F_{3,\mathbb Q}(y).
```

可加性定理要求 x±1、y±1、x+y 都非零；在 x,y>1 时这些条件自动满足。结合律在这个闭合正有理数域上给出。它不保证整数性或素数性，也未把此域称为带单位元的群。

## 3. 相关公式：已完成哪些，尚未完成哪些

定义有限截断

```math
v_{3,R}(n)=\sum_{j=1}^{R}\mathbf1_{3^j\mid n},\qquad
F_{3,R}(n)=v_{3,R}(n+1)-v_{3,R}(n-1).
```

已证明 n≠0 时 v₃,R(n)=min(R,v₃(n))；n≥1 时 F₃,R(n+3ᴿ)=F₃,R(n)。还证明了

```math
\sum_{i=0}^{N-1}F_3(i+2)=v_3(N+1)+v_3(N+2).
```

**v₃,R(0)=R，而 mathlib 的 v₃(0)=0。** 这两个全函数约定不能混用；相应边界已加回归证明。

此前纸面推导的相关极限

```math
\lim_{X\to\infty}\frac1X\sum_{n=2}^{X}F_3(n)F_3(n+h)
=|h-2|_3+|h+2|_3-2|h|_3
```

本轮**尚未完成 Lean 证明**。目前形式化的是它的有限截断基础，不是该极限，也不是任何素数子集上的相关结论。仍需完成有限周期重叠计数、均方尾部界及极限交换。

其他尚未完成的分析层内容：

- 三进对数 L(n)=log₃-ad U(n) 的收敛、同态性与等距性。此轮只形式化其前置的整数坐标 U。
- 限制素数乘子的精确升层密度。需要素数在固定等差数列中的渐近计数；有限余数计算不代替它。
- 前一轮文献层的素数单点分布和连续素数同值段，形式化状态保持不变。

这些未完成项没有放进默认 import 中成为公理，也没有用假设同名结论来制造“已证明”的表象。

## 4. 核验与复现

固定的 Lean 4.34.0 和 mathlib 修订不变。完整核验：

```sh
python3 scripts/verify.py
```

包括库构建、三组 Lean 回归模块、全部 `#print axioms`、源码禁用项检查、新增的审计覆盖检查及原有 Python 检查。`check_audit_coverage.py` 要求每条项目 theorem/lemma 在审计表中恰好出现一次；它不取代实际内核公理审计。

原始深层有限计算脚本在本次会话另行重跑：30,550 项精确检查通过。这是计算证据，不计为 Lean 定理。

本轮复用的底层定理：固定 mathlib 的 `Mathlib/NumberTheory/Multiplicity.lean`（提升指数）、`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`（有理赋值）、`Mathlib/Data/ZMod/Basic.lean` 与 `Mathlib/GroupTheory/OrderOfElement.lean`（实际阶）。

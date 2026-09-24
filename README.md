# Ω 与质因数和平衡素数：定理与猜想地图

本仓库形式化 Ω 计重个数平衡、质因数计重求和平衡、两者的双平衡，以及素数邻数的三进赋值差分。已形式化定理与尚未证明的猜想分区列出。

## 记号

$\Omega(n)$ 表示质因数总个数，**按重数计**；$S(n)$ 表示质因数本身计重求和；$v_q(n)$ 表示素因子 $q$ 的指数。对 $n>1$，记

$$
\begin{aligned}
F_\Omega(n)&=\Omega(n+1)-\Omega(n-1),&T_\Omega(n)&=\Omega(n-1)+\Omega(n+1),\\
F_\Sigma(n)&=S(n+1)-S(n-1),&F_3(n)&=v_3(n+1)-v_3(n-1).
\end{aligned}
$$

| Lean 定义 | 数学含义 |
|---|---|
| `bigOmega` | $\Omega(n)$，质因数计重**个数** |
| `omegaDiff`、`omegaSum` | $F_\Omega(n)$、$T_\Omega(n)$；`omegaSum` 不是质因数求和 |
| `primeFactorSum`、`primeFactorSumDiff` | $S(n)$、$F_\Sigma(n)$ |
| `primeFactorDefect` | $D(n)=n-S(n)$ |
| `f3` | $F_3(n)$ |
| `IsOmegaBalancedPrime p` | $p$ 为素数且左右 Ω 相等 |
| `IsPrimeFactorSumBalancedPrime p` | $p$ 为素数且左右 S 相等 |
| `IsDoubleBalancedPrime p k` | $p$ 为素数、左右 S 相等，且左右 Ω 均为 $k$ |

所有差分在整数中计算。下表定理位于 `OmegaBalance` 命名空间，链接指向形式化源码。

## Ω 与 F₃ 主定理地图

| 主定理 | 前提 | 数学结论 | Lean 定理 |
|---|---|---|---|
| **孪生素数的精确反号** | $p,p+2$ 均为素数，$p>3$ | $F_3(p+2)=-F_3(p)$，且两者均非零 | [`f3_twin`](OmegaBalance/F3.lean) |
| **精确反号的同余推广** | $n>1$，$n\equiv2\pmod3$，不要求素数性 | $F_3(n+2)=-F_3(n)$，且两者均非零 | [`f3_opposite_of_mod_three`](OmegaBalance/F3.lean) |
| **Ω 平衡的零点刻画** | $p\ge2$ | $p$ 为 Ω 平衡素数，当且仅当 $p$ 为素数且 $F_\Omega(p)=0$ | [`isOmegaBalancedPrime_iff`](OmegaBalance/Basic.lean) |
| **奇数邻项约去公共因子 2** | $n>1$ 为奇数 | $F_\Omega(n)=\Omega((n+1)/2)-\Omega((n-1)/2)$；平衡等价于两个相邻半邻数的 Ω 相等 | [`omegaDiff_eq_half_diff`](OmegaBalance/Basic.lean)、[`isOmegaBalanced_iff_half`](OmegaBalance/Basic.lean) |
| **邻项总计数的乘积公式** | $n>1$ | $T_\Omega(n)=\Omega((n-1)(n+1))=\Omega(n^2-1)$ | [`omegaSum_eq_bigOmega_product`](OmegaBalance/Basic.lean)、[`omegaSum_eq_bigOmega_sq_sub_one`](OmegaBalance/Basic.lean) |

## 质因数和与双平衡主定理地图

| 主定理 | 前提 | 数学结论 | Lean 定理 |
|---|---|---|---|
| **五素数参数族** | `SumFamilyPrimeValues t`：指定的两个一次式、两个二次式和中心三次式均为素数 | 中心 $P(t)$ 为 S 平衡素数；左右 Ω 分别为 5、4，总计数 9，Ω 差为 −1 | [`sumFamily_five_primes`、`sumFamily_left_profile`、`sumFamily_right_profile`](OmegaBalance/FactorSumFamily.lean) |
| **低总计数完整分类** | 任意自然数 $p$ | $p$ 为 S 平衡素数且 $T_\Omega(p)\le8$，当且仅当 $p\in\{11,17,31\}$ | [`sumBalanced_total_le_eight_iff`](OmegaBalance/FactorSumLowCount.lean) |
| **双平衡的最小可达级数** | 两邻数同时求和平衡、且 Ω 均为 $k$ | 必有 $k\ge5$；确实存在 $k=5$ 的素数 | [`doubleBalanced_level_ge_five`](OmegaBalance/FactorSumStructure.lean)、[`doubleBalanced_minimum_level`](OmegaBalance/FactorSumExamples.lean) |
| **五级双平衡完整形状** | $p$ 为素数 | 五级双平衡等价于 $\{p-1,p+1\}=\{6bcd,8rs\}$，其中 $b,c,d,r,s$ 为奇素数且 $r+s+1=b+c+d$；同侧可重复因子 | [`doubleBalanced_five_shape_iff`](OmegaBalance/FactorSumFive.lean) |
| **双平衡孪生限制** | $p,p+2$ 分别为 $k,j$ 级双平衡素数 | $k=j\ge6$；五级双平衡素数不能成孪生对 | [`doubleBalanced_twins_level_ge_six`、`doubleBalanced_five_not_twins`](OmegaBalance/FactorSumFive.lean) |

五参数族的具体表达式、接口和证明依赖见[求和平衡形式化地图](docs/sum_balance/formalization.md)。上述构造是带显式素性前提的蕴含，不声称已经证明了无穷多个参数同时为素数。

## 质因数和的运算与结构推论

| 结论 | 前提与数学内容 | Lean 定理 |
|---|---|---|
| 完全可加性与素数幂 | $a,b>0$ 时 $S(ab)=S(a)+S(b)$；素数 $q$ 满足 $S(q^k)=kq$ | [`primeFactorSum_mul`、`primeFactorSum_prime_pow`](OmegaBalance/FactorSum.lean) |
| 大小界与素数刻画 | $S(n)\le n$；$n>0$ 时，等号当且仅当 $n$ 为素数或 $n=4$ | [`primeFactorSum_le`、`primeFactorSum_eq_self_iff`](OmegaBalance/FactorSumArithmetic.lean) |
| 零点与半邻数 | $F_\Sigma(n)=0$ 等价于左右 S 平衡；奇数 $n>1$ 可同时约去邻数中的一个因子 2 | [`primeFactorSumDiff_eq_zero_iff`、`primeFactorSumBalanced_iff_half`](OmegaBalance/FactorSum.lean) |
| 一般余因子构造 | $A,B>0$，$q,r$ 素数，$Br=Aq+1$ 且 $S(A)+q=S(B)+r$；若 $2Aq+1$ 为素数，则它求和平衡 | [`primeFactorSum_cofactor_construction`](OmegaBalance/FactorSum.lean) |
| 精确缺陷公式 | 参数族中只要求 U、V 为素数；Q、R 允许合数 | $F_\Sigma(P)=D(Q)-D(R)$；平衡当且仅当两个缺陷相等 | [`sumFamily_defect_identity`、`sumFamily_balanced_iff_defect`](OmegaBalance/FactorSumFamily.lean) |
| 奇偶耦合 | $S(n)+v_2(n)\equiv\Omega(n)\pmod2$；S 平衡时 $F_\Omega(n)\equiv v_2(n+1)-v_2(n-1)\pmod2$ | [`primeFactorSum_parity`、`sumBalanced_count_valuation_parity`](OmegaBalance/FactorSumArithmetic.lean) |
| 双平衡的模 8 限制 | 任意级数双平衡素数满足 $p\equiv1$ 或 $7\pmod8$ | [`doubleBalanced_mod_eight`](OmegaBalance/FactorSumArithmetic.lean) |
| 五级的模 48 限制 | 五级双平衡素数满足 $p\equiv7$ 或 $41\pmod{48}$ | [`doubleBalanced_five_mod_forty_eight`](OmegaBalance/FactorSumFive.lean) |
| 其余 S 平衡素数的总计数 | 排除 $11,17,31$ 后，必有 $T_\Omega(p)\ge9$ | [`sumBalanced_total_ge_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 固定总计数的无穷性下界 | **若**某个总计数 $k$ 层有无穷多个 S 平衡素数，则 $k\ge9$ | [`infinite_sumBalanced_level_ge_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 参数无穷性的传递 | **若**五项素数参数集合无限，则总计数 9 的 S 平衡素数集合无限；定理不证明其输入前提 | [`infinite_sumFamily_implies_level_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 五级因数对恒等式 | 整数 $d=r+s-L$ 时，$4rs-Kd=e$ 等价于 $(4r-K)(4s-K)=K(K-4L)+4e$ | [`doubleFactorPair_iff`](OmegaBalance/FactorSumFamily.lean) |

## 孪生素数及三进赋值的推论

下表前五行均假设 $p,p+2$ 为素数且 $p>3$；最后两行只要求 $p>3$ 为素数。

| 推论 | 数学结论 | Lean 定理 |
|---|---|---|
| 共享邻数给出精确幅度 | $F_3(p)=v_3(p+1)>0$，$F_3(p+2)=-v_3(p+1)$ | [`f3_twin_values`](OmegaBalance/F3.lean) |
| 符号方向固定 | $F_3(p)>0$，$F_3(p+2)<0$ | [`f3_twin_signs`](OmegaBalance/F3.lean) |
| 绝对值相等 | $\lvert F_3(p+2)\rvert=\lvert F_3(p)\rvert$ | [`f3_twin_abs_eq`、`f3_twin_natAbs_eq`](OmegaBalance/F3.lean) |
| 乘积严格为负 | $F_3(p)F_3(p+2)<0$ | [`f3_twin_mul_neg`](OmegaBalance/F3.lean) |
| 模六结构 | $p\equiv5\pmod6$，$6\mid p+1$；存在 $k>0$ 使 $p=6k-1$、$p+2=6k+1$ | [`twin_mod_six`、`six_dvd_twin_center`、`twin_six_mul_form`](OmegaBalance/F3.lean) |
| 大于三的素数均非零 | $F_3(p)\ne0$ | [`f3_ne_zero_of_prime`](OmegaBalance/F3.lean) |
| 符号由模三余数刻画 | $F_3(p)>0\iff p\equiv2\pmod3$；$F_3(p)<0\iff p\equiv1\pmod3$ | [`f3_pos_iff_mod_three`、`f3_neg_iff_mod_three`](OmegaBalance/F3.lean) |

## Ω 平衡与赋值的相关结论

| 结论 | 前提与数学内容 | Lean 定理 |
|---|---|---|
| 一般中心的零点判据 | $n>1$ 时，$F_\Omega(n)=0\iff\Omega(n-1)=\Omega(n+1)$，不要求素数性 | [`omegaDiff_eq_zero_iff`](OmegaBalance/Basic.lean) |
| 素数邻项约去因子 2 | 素数 $p>2$ 满足 $F_\Omega(p)=\Omega((p+1)/2)-\Omega((p-1)/2)$ | [`omegaDiff_prime_eq_half_diff`](OmegaBalance/Basic.lean) |
| 和差恢复左右计数 | $T_\Omega(n)+F_\Omega(n)=2\Omega(n+1)$，$T_\Omega(n)-F_\Omega(n)=2\Omega(n-1)$；等式在整数中理解 | [`omegaSum_add_omegaDiff`、`omegaSum_sub_omegaDiff`](OmegaBalance/Basic.lean) |
| Ω 的完全可加性与素数幂 | $a,b>0$ 时 $\Omega(ab)=\Omega(a)+\Omega(b)$；素数 $q$ 满足 $\Omega(q^k)=k$ | [`bigOmega_mul`、`bigOmega_prime_pow`](OmegaBalance/Basic.lean) |
| 赋值与整除等价 | 素数 $q$、$n>0$ 满足 $v_q(n)>0\iff q\mid n$ | [`valuation_pos_iff_dvd`](OmegaBalance/Valuation.lean) |
| 赋值的乘法与幂 | 素数 $q$、$a,b>0$ 满足 $v_q(ab)=v_q(a)+v_q(b)$；$v_q(q^k)=k$ | [`valuation_mul`、`valuation_prime_pow`](OmegaBalance/Valuation.lean) |

## F₃ 的整数延拓与运算定理

`f3Int : ℤ → ℤ` 保留原 `f3 : ℕ → ℤ`。以下结果不要求素数性；非零及互素前提见对应源码与 [F₃ 整数延拓说明](docs/f3_extension.md)。

| 内容 | 数学结论与范围 | Lean 接口 |
|---|---|---|
| 整数兼容与奇函数 | $n\ge1$ 时 `f3Int n = f3 n`；所有整数满足 `f3Int (-z) = -f3Int z` | [`f3Int_nat`、`f3Int_neg`](OmegaBalance/F3Extension.lean) |
| 零点分类 | $n>1$ 时，$F_3(n)=0\iff3\mid n$ | [`f3_eq_zero_iff_three_dvd`](OmegaBalance/F3Extension.lean) |
| 平方 | $n>1,3\nmid n$ 时，$F_3(n^2)=-\lvert F_3(n)\rvert$ | [`f3_sq`](OmegaBalance/F3Extension.lean) |
| 立方与迭代立方 | $n>1,3\nmid n$ 时，符号不变，每次立方使层级增加 1 | [`f3_cube`](OmegaBalance/F3Extension.lean)、[`f3_iterated_cube_pos`、`f3_iterated_cube_neg`](OmegaBalance/F3Arithmetic.lean) |
| 乘法 | $m,n>1,3\nmid mn$ 时，层级至少为两个输入层级的较小值；异层时恰取较小者，符号有精确规则 | [`f3_mul_depth`、`f3Side_mul`](OmegaBalance/F3Arithmetic.lean) |
| 修正间距 | 输入层级不同时，修正间距的赋值恰为较小层级；使用整数差 | [`f3_adjusted_gap_valuation`](OmegaBalance/F3Arithmetic.lean) |
| 固定和反射 | $a,b>1,3\nmid a,3\mid a+b$ 且 $\lvert F_3(a)\rvert<v_3(a+b)$ 时，$F_3(b)=-F_3(a)$ | [`f3_reflection`](OmegaBalance/F3Arithmetic.lean) |

## F₃ 深层推论的形式化接口

以下入口及精确前提见 [F₃ 深层形式化地图](docs/f3_deeper_formalization.md)。

| 内容 | 主要结论 | Lean 接口 |
|---|---|---|
| 任意正整数幂 | 层级增加 $v_3(e)$，符号由底数余数及指数奇偶决定 | [`f3_pow_depth`、`f3Side_pow`、`f3_pow`](OmegaBalance/F3Powers.lean) |
| 有理延拓与 Cayley 运算 | $\Phi((x y+1)/(x+y))=\Phi(x)+\Phi(y)$；保留零点与极点例外 | [`f3Rat_star`、`f3Rat_star_of_gt_one`](OmegaBalance/F3Rational.lean) |
| Cayley 结合律 | $x,y,z>1$ 时 $x\star y=(xy+1)/(x+y)$ 结合，Cayley 变换将它变为乘法 | [`f3Cayley_star`、`f3Cayley_involution`、`f3Star_assoc`](OmegaBalance/F3Rational.lean) |
| 反号配对的和积关系 | $n-m=2+3^kT$ 时，$v_3(mn-1)$ 与 $v_3(m+n)$ 的较小者由 $v_3(T)$ 决定 | [`f3_opposite_sum_product`、`f3_product_refined_gap`](OmegaBalance/F3SumProduct.lean) |
| 孪生乘积与间距阈值 | 孪生对满足 $F_3(p(p+2))=2F_3(p)$；推出乘积阈值下的间距二择一 | [`f3_twin_product`、`f3_product_gap_dichotomy`](OmegaBalance/F3SumProduct.lean) |
| 模 $3^k$ 的乘法阶 | 依正负侧得到阶 $3^{\max(k-a,0)}$ 或其两倍；孪生对的阶相差两倍 | [`f3_orderOf`、`f3_twin_orderOf`](OmegaBalance/F3Order.lean) |
| 同层进位判据 | 首单位数字和模 3 为零，当且仅当乘积层级严格上升 | [`f3_same_level_cancellation`、`f3_same_level_rises_iff`](OmegaBalance/F3Coordinates.lean) |
| 原根塔判据 | $F_3(n)=1$ 等价于模 9 的阶为 6，也等价于所有 $3^k$ 上达到最大阶 | [`f3_eq_one_iff_order_nine`、`f3_eq_one_iff_maximal_order_tower`](OmegaBalance/F3Primitive.lean) |
| 有限截断与望远镜求和 | 截断函数以 $3^K$ 为周期，等于截断后的 $F_3$；连续整数求和只剩边界项 | [`f3Trunc_periodic`、`f3Trunc_eq_clipped`、`f3_sum_range`](OmegaBalance/F3Finite.lean) |

## 已形式化的实例与反例

| 实例或反例 | 已证明的结论 | Lean 定理 |
|---|---|---|
| Ω 平衡实例 $p=5$ | $5$ 是 Ω 平衡素数 | [`five_isOmegaBalancedPrime`](OmegaBalance/Examples.lean) |
| 小 S 平衡实例 | $11,17,31$ 均为求和平衡素数 | [`sumBalanced_11`、`sumBalanced_17`、`sumBalanced_31`](OmegaBalance/FactorSumExamples.lean) |
| 参数族实例 | $t=5$ 的五项均为素数，中心 $3615811$ 求和平衡，Ω 总计数 9、差 −1 | [`sumFamily_prime_values_five`、`sumBalanced_3615811`、`sumBalanced_3615811_profile`](OmegaBalance/FactorSumExamples.lean) |
| 五级双平衡实例 | $870404071$、$748465063$ 两个中心及各因子的素性均被证明，左右均为五个因子且总和相等 | [`doubleBalanced_870404071`、`doubleBalanced_748465063`](OmegaBalance/FactorSumExamples.lean) |
| 孪生对 $(17,19)$ | $F_3(17)=2$，$F_3(19)=-2$ | [`twin_seventeen_nineteen_example`](OmegaBalance/Examples.lean) |
| 例外孪生对 $(3,5)$ | $F_3(3)=0$、$F_3(5)=1$；主定理的 $p>3$ 不能删去 | [`exceptional_twin_three`](OmegaBalance/Examples.lean) |
| 反号不是孪生的充分条件 | 素数 $5,13$ 的 F₃ 值是非零相反数，但不是孪生对 | [`opposite_f3_not_sufficient_for_twins`](OmegaBalance/Examples.lean) |
| F₃ 对称性不能移植到 Ω 差分 | 孪生对 $(5,7)$ 满足 $F_\Omega(5)=0$、$F_\Omega(7)=1$ | [`omegaDiff_twin_five_seven`](OmegaBalance/Examples.lean) |
| F₃ 两标量不能确定乘积 | $F_3(5)=F_3(11)=1$，但与 7 相乘后分别得到 −2 与 −1 | [`f3_no_scalar_mul_rule`](OmegaBalance/F3DeeperExamples.lean) |

## 猜想地图（未证明）

令 $\mathcal B=\{p>2:p\text{ 为素数且 }\Omega(p-1)=\Omega(p+1)\}$。这里是 **Ω 计重个数平衡**，不是质因数求和的 S 平衡。默认允许 $p=q$，不要求两个加数的平衡级数相同。

**以下不是已证定理；有限验算不是无限范围证明，也没有作为 Lean 公理加入。**

| 编号 | 猜想 | 精确陈述 | 当前证据与状态 |
|---|---|---|---|
| [OBG-1](docs/conjectures/omega_balanced_goldbach.md#obg-1) | **充分大偶数覆盖** | 存在 $N_0$，每个整数 $N\ge N_0$ 都有 $p,q\in\mathcal B$ 使 $2N=p+q$ | 未证明；有限计算支持 |
| [OBG-2](docs/conjectures/omega_balanced_goldbach.md#obg-2) | **显式起点版** | 每个整数 $N\ge259\,299$ 都有这样的表示，即覆盖全部偶数 $2N\ge518\,598$ | 未证明；已验算每个偶数 $518\,598\le2N\le10^8$ |
| [OBG-3](docs/conjectures/omega_balanced_goldbach.md#obg-3) | **不同加数加强版** | OBG-2 中进一步要求 $p<q$ | 未证明；同一区间有限验算仍成立 |

**OBG-3 ⇒ OBG-2 ⇒ OBG-1**。一亿以内的 3,088 个不可表示偶数最大为 518,596，不代表一亿以外没有例外。“覆盖全体偶数”已被 100 等反例否定，不列为开放猜想。详见[猜想档案与验算范围](docs/conjectures/omega_balanced_goldbach.md)。

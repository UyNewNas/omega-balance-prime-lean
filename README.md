# Ω 平衡素数：定理与猜想地图

本仓库形式化了 Ω 平衡判据、素数邻数的赋值差分，以及孪生素数的三进赋值精确反号定理及其推论。已形式化定理与尚未证明的猜想分区列出。

## 记号

$\Omega(n)$ 表示质因数总个数，**按重数计**；$v_q(n)$ 表示正整数 $n$ 中素因子 $q$ 的指数。对 $n>1$，记

$$
F_\Omega(n)=\Omega(n+1)-\Omega(n-1),\qquad
T_\Omega(n)=\Omega(n-1)+\Omega(n+1),\qquad
F_3(n)=v_3(n+1)-v_3(n-1).
$$

对应 Lean 定义为 `omegaDiff`、`omegaSum`、`f3`；差分均在整数中计算。$T_\Omega$ 是左右质因数**个数**之和，不是质因数本身的求和。Ω 平衡素数指满足 $\Omega(p-1)=\Omega(p+1)$ 的素数 $p$。

下表中的定理均位于 `OmegaBalance` 命名空间，链接指向其形式化源码。

## 主定理地图

| 主定理 | 前提 | 数学结论 | Lean 定理 |
|---|---|---|---|
| **孪生素数的精确反号** | $p,p+2$ 均为素数，$p>3$ | $F_3(p+2)=-F_3(p)$，且两者均非零 | [`f3_twin`](OmegaBalance/F3.lean) |
| **精确反号的同余推广** | $n>1$，$n\equiv2\pmod3$，不要求素数性 | $F_3(n+2)=-F_3(n)$，且两者均非零 | [`f3_opposite_of_mod_three`](OmegaBalance/F3.lean) |
| **Ω 平衡的零点刻画** | $p\ge2$ | $p$ 为 Ω 平衡素数，当且仅当 $p$ 为素数且 $F_\Omega(p)=0$ | [`isOmegaBalancedPrime_iff`](OmegaBalance/Basic.lean) |
| **奇数邻项约去公共因子 2** | $n>1$ 为奇数 | $F_\Omega(n)=\Omega((n+1)/2)-\Omega((n-1)/2)$；左右平衡等价于这两个相邻整数的 Ω 相等 | [`omegaDiff_eq_half_diff`](OmegaBalance/Basic.lean)、[`isOmegaBalanced_iff_half`](OmegaBalance/Basic.lean) |
| **邻项总计数的乘积公式** | $n>1$ | $T_\Omega(n)=\Omega((n-1)(n+1))=\Omega(n^2-1)$ | [`omegaSum_eq_bigOmega_product`](OmegaBalance/Basic.lean)、[`omegaSum_eq_bigOmega_sq_sub_one`](OmegaBalance/Basic.lean) |

## 孪生素数及三进赋值的推论

下表前五行均假设 $p,p+2$ 为素数且 $p>3$；最后两行只要求 $p>3$ 为素数。

| 推论 | 数学结论 | Lean 定理 |
|---|---|---|
| 共享邻数给出精确幅度 | $F_3(p)=v_3(p+1)>0$，$F_3(p+2)=-v_3(p+1)$ | [`f3_twin_values`](OmegaBalance/F3.lean) |
| 符号方向固定 | $F_3(p)>0$，$F_3(p+2)<0$ | [`f3_twin_signs`](OmegaBalance/F3.lean) |
| 绝对值相等 | $\lvert F_3(p+2)\rvert=\lvert F_3(p)\rvert$ | [`f3_twin_abs_eq`](OmegaBalance/F3.lean)、[`f3_twin_natAbs_eq`](OmegaBalance/F3.lean) |
| 乘积严格为负 | $F_3(p)F_3(p+2)<0$ | [`f3_twin_mul_neg`](OmegaBalance/F3.lean) |
| 孪生对的模六结构 | $p\equiv5\pmod6$，$6\mid p+1$；存在 $k>0$ 使 $p=6k-1$、$p+2=6k+1$ | [`twin_mod_six`](OmegaBalance/F3.lean)、[`six_dvd_twin_center`](OmegaBalance/F3.lean)、[`twin_six_mul_form`](OmegaBalance/F3.lean) |
| 所有大于三的素数均非零 | $F_3(p)\ne0$ | [`f3_ne_zero_of_prime`](OmegaBalance/F3.lean) |
| 符号由模三余数刻画 | $F_3(p)>0\iff p\equiv2\pmod3$；$F_3(p)<0\iff p\equiv1\pmod3$ | [`f3_pos_iff_mod_three`](OmegaBalance/F3.lean)、[`f3_neg_iff_mod_three`](OmegaBalance/F3.lean) |

## Ω 平衡与赋值的相关结论

| 结论 | 前提与数学内容 | Lean 定理 |
|---|---|---|
| 一般中心的零点判据 | $n>1$ 时，$F_\Omega(n)=0\iff\Omega(n-1)=\Omega(n+1)$，不要求 $n$ 为素数 | [`omegaDiff_eq_zero_iff`](OmegaBalance/Basic.lean) |
| 素数邻项约去公共因子 2 | 素数 $p>2$ 满足 $F_\Omega(p)=\Omega((p+1)/2)-\Omega((p-1)/2)$ | [`omegaDiff_prime_eq_half_diff`](OmegaBalance/Basic.lean) |
| 和差恢复左右计数 | $n>1$ 时，$T_\Omega(n)+F_\Omega(n)=2\Omega(n+1)$，$T_\Omega(n)-F_\Omega(n)=2\Omega(n-1)$；等式在整数中理解 | [`omegaSum_add_omegaDiff`](OmegaBalance/Basic.lean)、[`omegaSum_sub_omegaDiff`](OmegaBalance/Basic.lean) |
| Ω 的完全可加性与素数幂计数 | $a,b>0$ 时 $\Omega(ab)=\Omega(a)+\Omega(b)$；素数 $q$、$k\ge0$ 满足 $\Omega(q^k)=k$ | [`bigOmega_mul`](OmegaBalance/Basic.lean)、[`bigOmega_prime_pow`](OmegaBalance/Basic.lean) |
| 赋值与整除的等价 | 素数 $q$、$n>0$ 满足 $v_q(n)>0\iff q\mid n$ | [`valuation_pos_iff_dvd`](OmegaBalance/Valuation.lean) |
| 赋值的乘法与幂公式 | 素数 $q$、$a,b>0$ 满足 $v_q(ab)=v_q(a)+v_q(b)$；$k\ge0$ 时 $v_q(q^k)=k$ | [`valuation_mul`](OmegaBalance/Valuation.lean)、[`valuation_prime_pow`](OmegaBalance/Valuation.lean) |

## 已形式化的实例与反例

| 实例或反例 | 已证明的结论 | Lean 定理 |
|---|---|---|
| Ω 平衡实例 $p=5$ | $5$ 是 Ω 平衡素数 | [`five_isOmegaBalancedPrime`](OmegaBalance/Examples.lean) |
| 孪生对 $(17,19)$ | $F_3(17)=2$，$F_3(19)=-2$ | [`twin_seventeen_nineteen_example`](OmegaBalance/Examples.lean) |
| 例外孪生对 $(3,5)$ | $F_3(3)=0$，$F_3(5)=1$，不满足精确反号；主定理的 $p>3$ 前提不能删除 | [`f3_three`](OmegaBalance/Examples.lean)、[`f3_five`](OmegaBalance/Examples.lean)、[`exceptional_twin_three`](OmegaBalance/Examples.lean) |
| 精确反号不是孪生的充分条件 | 素数 $5,13$ 的 $F_3$ 值为非零相反数，但两者不构成孪生对 | [`opposite_f3_not_sufficient_for_twins`](OmegaBalance/Examples.lean) |
| $F_3$ 对称性不能移植到完整 Ω 差分 | 孪生对 $(5,7)$ 满足 $F_\Omega(5)=0$、$F_\Omega(7)=1$ | [`omegaDiff_twin_five_seven`](OmegaBalance/Examples.lean) |

## F₃ 的整数延拓与运算定理

新增 `f3Int : ℤ → ℤ`，保留原 `f3 : ℕ → ℤ`。以下结果不需要素数身份；具体非零及互素条件显式写在源码中。完整数学推导见 [F₃ 整数延拓说明](docs/f3_extension.md)。

| 内容 | 数学结论与范围 | Lean 接口 |
|---|---|---|
| 整数兼容与奇函数 | $n\ge1$ 时 `f3Int n = f3 n`；所有整数满足 `f3Int (-z) = -f3Int z` | [`f3Int_nat`、`f3Int_neg`](OmegaBalance/F3Extension.lean) |
| 零点分类 | $n>1$ 时，$F_3(n)=0\iff3\mid n$ | [`f3_eq_zero_iff_three_dvd`](OmegaBalance/F3Extension.lean) |
| 平方 | $n>1,3\nmid n$ 时，$F_3(n^2)=-\lvert F_3(n)\rvert$ | [`f3_sq`](OmegaBalance/F3Extension.lean) |
| 立方与迭代立方 | 符号不变，每次立方使层级增加 1；前提 $n>1,3\nmid n$ | [`f3_cube`](OmegaBalance/F3Extension.lean)、[`f3_iterated_cube_pos`、`f3_iterated_cube_neg`](OmegaBalance/F3Arithmetic.lean) |
| 乘法 | $m,n>1,3\nmid mn$ 时，层级至少是两输入的较小者；异层时恰取较小者，符号也有精确规则 | [`f3_mul_depth`、`f3Side_mul`](OmegaBalance/F3Arithmetic.lean) |
| 修正间距 | 输入层级不同时，修正间距的赋值恰为较小层级；在整数中计算，不截断负差 | [`f3_adjusted_gap_valuation`](OmegaBalance/F3Arithmetic.lean) |
| 固定和反射 | $a,b>1,3\nmid a,3\mid a+b$ 且 $\lvert F_3(a)\rvert<v_3(a+b)$ 时，$F_3(b)=-F_3(a)$；总和可为奇数 | [`f3_reflection`](OmegaBalance/F3Arithmetic.lean) |

本轮另有 [8 条内核回归证明](OmegaBalance/F3Examples.lean)，以及 [千万以内计算报告](reports/f3_corollaries_1e7.txt)：144,240 项有限检查与 11 组边界测试。有限检查不代替 Lean 证明；等差数列素数密度与连续素数同值段只在文档中引用外部定理，没有添加为 Lean 公理。

复现完整检查（先安装固定工具链并获取依赖）：

```sh
python3 scripts/verify.py
```

## 猜想地图（未证明）

令 $\mathcal B=\{p>2:p\text{ 为素数且 }\Omega(p-1)=\Omega(p+1)\}$。这里是最初的 **Ω 计重个数平衡**，不是质因数求和的 $S$ 平衡。默认允许 $p=q$，不要求两个加数的平衡级数相同。

**以下是待证明命题，不属于上方的已形式化定理；有限验算不是无限范围证明，也没有作为 Lean 公理加入。**

| 编号 | 猜想 | 精确陈述 | 当前证据与状态 |
|---|---|---|---|
| [OBG-1](docs/conjectures/omega_balanced_goldbach.md#obg-1) | **充分大偶数覆盖** | 存在 $N_0$，对每个整数 $N\ge N_0$，存在 $p,q\in\mathcal B$ 使 $2N=p+q$ | 未证明；有限计算支持 |
| [OBG-2](docs/conjectures/omega_balanced_goldbach.md#obg-2) | **显式起点版** | 对每个整数 $N\ge259\,299$，存在 $p,q\in\mathcal B$ 使 $2N=p+q$，即覆盖全部偶数 $2N\ge518\,598$ | 未证明；已验算每个偶数 $518\,598\le2N\le10^8$ |
| [OBG-3](docs/conjectures/omega_balanced_goldbach.md#obg-3) | **不同加数加强版** | OBG-2 中进一步要求 $p<q$ | 未证明；同一区间的有限验算仍成立 |

关系为 **OBG-3 ⇒ OBG-2 ⇒ OBG-1**。一亿以内共发现 **3,088** 个不可表示偶数，最大为 **518,596**；这不是对一亿以外无例外的证明。原始“覆盖全体偶数”版本已被 $100$ 等反例否定，不列为开放猜想。

[猜想档案、反例与验算范围](docs/conjectures/omega_balanced_goldbach.md)收录完整量词、计算证据及复现方法；这些内容均与 Lean 定理地图分开维护。

## F₃ 深层推论：形式化代码地图

完整前提、依赖与尚未形式化的分析结论见 [深层推论覆盖说明](docs/f3_deeper_formalization.md)。保持原有 API，并新增以下模块：

| 模块 | 内容 |
|---|---|
| [F3Powers](OmegaBalance/F3Powers.lean) | 任意正指数的完整幂公式，复用 mathlib 提升指数定理 |
| [F3Order](OmegaBalance/F3Order.lean)、[F3Primitive](OmegaBalance/F3Primitive.lean) | 实际 `ZMod` 乘法阶塔、孪生阶比、F₃=1 的最大阶／原根判据 |
| [F3SumProduct](OmegaBalance/F3SumProduct.lean) | 和积层级二分、孪生乘积加倍、附加乘积条件下的加强间距 |
| [F3Coordinates](OmegaBalance/F3Coordinates.lean) | 正规化单位坐标、同层抵消的精确多项式、首次升层判据 |
| [F3Rational](OmegaBalance/F3Rational.lean) | 有理数延拓、Cayley 共轭、星运算严格可加及结合律 |
| [F3Finite](OmegaBalance/F3Finite.lean) | 有限整除层展开、精确周期与望远镜求和 |
| [F3DeeperExamples](OmegaBalance/F3DeeperExamples.lean) | 新的内核回归证明及标量乘法规则不可能性定理 |

`python3 scripts/verify.py` 现在也检查第三组 Lean 回归模块和 [公理审计覆盖](scripts/check_audit_coverage.py)：每条项目 theorem/lemma 必须登记一次。

**尚未完成 Lean 证明：** 三进对数坐标的分析性质、限制素数乘子的渐近升层密度、完整无限相关核及均方近似周期。相关核目前仅有有限截断基础，不把纸面或 Python 结论当成内核已证定理。

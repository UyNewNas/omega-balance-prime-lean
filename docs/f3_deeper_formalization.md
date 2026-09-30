# F₃ 深层推论：形式化覆盖与边界

## 2026-09-30 07:16 UTC：无条件 RUN 精确验证及最新主线组合

无条件代码 `69c48f9e74426ef8004a761752c59d524f2d7fdb` 的
[push 36679099690](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679099690) 与
[PR 36679105586](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679105586)
全部成功。实际日志中 `MaynardBFT.consecutive_primes`、
`OmegaBalance.bftbPrimeIndexRuns_unconditional`、
`OmegaBalance.f3PrimeIndexRunStarts_infinite_unconditional` 均仅依赖
`propext`、`Classical.choice`、`Quot.sound`。完整产生器、项目构建、内核回归、
650 个依赖模块源码/固定版本检查、99 个项目文件、646+1 精确审计和144240有限检查通过。

最终接口是：每个 L≥1 存在仅依赖 L 的自然数 C，对每个非零整数 c，
全体素数枚举 `Nat.nth Nat.Prime` 中有无限多个起始下标 r，使连续 L 个素数
的 F₃ 全为 c，且末首素数之差≤`f3RunModulus c * C`。长度1保留零跨度情形。
`F3PrimeIndexRunAt` 明确使用全体素数，不是某个筛选子列；原条件接口由实际
上游定理产生，不再作为未经证明的前提。

新增五条声明：`bftbPrimeIndexRuns_unconditional`、
`f3PrimeIndexRunStarts_infinite_unconditional`（F3BFTBMaynardAdapter），以及
`bftb_eventually_log_rpow_le_rpow`、`bftb_eventually_rpow_le_half_rpow_div_rpow_log`、
`bftb_eventually_floor_rpow_le_floor_half_rpow_div_rpow_log`（F3BFTBCutoff）。
原始固定 Lean/mathlib、真实参数边界和全部审计门禁保持不变。第三方来源说明
继续如实标注作者代码许可范围尚未确认；不把署名或沉默解释为许可。

随后真实三方合入已验 Haar 主线 `f45cd8a7586609555e8f307d25c38fee5c105249`，
保留双方全部数学源码字节及文档。组合候选是684条项目声明+1必需上游产生器、
105个项目文件；本地15项兼容测试、6项审计规则测试与源码/覆盖检查通过。
这个新增组合树仍须自己的完整 CI，不能用69c48f9的旧run替代。

原五项目标中的 INF/COR/DEN/LOG 已在主线；RUN 已有无条件内核证明，等待最新
组合验证与合并。全部接收 proof 任务尚未完成：全局 PAT、REC 等剩余概率/等待律、
其它登记节点继续开放。单次 Haar 范围已合入 PR51，不扩张为完整 REC 完成。


## 2026-09-30 当前覆盖更新（优先于下方历史轮次）

组合代码 `febe6175d83d8f2fa92b6f8a3d2b610016119a22` 的 [PR Lean run 36660504382](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36660504382) 与 [push run 36660499386](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36660499386) 全部通过。601条项目声明的实际公理输出仅标准Lean公理；94源文件与一对一覆盖通过，144240有限回归通过。锁定Lean4.34.0/mathlib5ed2965不变，实际解析的ANT099d3726依赖清单已提交。下方“尚未完成”描述是2026-09-24历史，不再用作当前状态。

- COR-1：`F3CorrelationLimitExchange.tendsto_f3CorrelationIccAverage` 对实际2≤n≤N的整数平均证明完整核；并非素数子集平均。
- COR-2：`F3CorrelationShiftSquare.tendsto_f3MeanSquareShiftIccAverage_pow_three` 对r>0给出4/3^r；r=0平移1极限单独为16/3。
- LOG-1：真正收敛级数 `f3PadicLog`，`f3PadicLog_valuation`、`f3_eq_neg_chi_mul_log_valuation` 与 `f3PadicLog_mul`，域n>1且3∤n；整数U没有冒充log。
- DEN-1：`F3PrimeDensityExactPos/ExactNeg/Tail` 给出精确素数计数相对于x/log x的常数；显式全体素数计数分母的比例接口随后在 `F3PrimeRelativeDensity.lean` 的代码70becdbf完整验证。
- DEN-2：`f3PrimeMul17EqTwoRelativeRatio_tendsto` 与 `f3PrimeMul17HighRelativeRatio_tendsto` 给出条件比例1/2与3^-j，j>0。
- PAT-L1–3：`F3FourPrimePattern.lean` 已合入59be8b23；全局PAT外部依赖及无条件RUN仍未完成。

[完整任务及验收边界](f3_formalization_tasks.md) · [来源接收与新增待办](f3_proof_intake.md) · [外部复用及信任记录](f3_external_reuse.md)。本记录后的文档提交另验精确CI；不将旧run当新head。


日期：2026-09-24。本轮将此前 `deeper_corollaries.md` 的局部算术推论整理为 Lean 证明，并逐步补上相关计算的有限基础。**不是全部分析结论均已形式化。** 是否通过内核检查，以对应提交的 Lean CI、公理日志及覆盖检查为准。

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
| 完整 `3^R` 周期内幂三余数类的精确重叠计数 | `card_filter_range_modEq_pow_three`, `modPairCount_eq_of_le`, `modPairCount_eq` | [F3CorrelationFinite.lean](../OmegaBalance/F3CorrelationFinite.lean) |

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

进一步，若 j,k≤R，则完整周期 `0≤n<3^R` 中两个余数条件的交集已精确形式化为

```math
\#\{n:n\equiv a\pmod{3^j},\ n\equiv b\pmod{3^k}\}
=
\begin{cases}
3^{R-\max(j,k)},&a\equiv b\pmod{3^{\min(j,k)}},\\
0,&\text{否则}.
\end{cases}
```

这正是展开截断相关时所需的有限重叠输入，但**仍不是**截断相关的闭式、尾部控制或无限极限。

此前纸面推导的相关极限

```math
\lim_{X\to\infty}\frac1X\sum_{n=2}^{X}F_3(n)F_3(n+h)
=|h-2|_3+|h+2|_3-2|h|_3
```

仍**尚未完成 Lean 证明**。当前已完成有限截断与完整周期余数重叠；下一步是把四类指标函数乘积展开成有限双重和并作几何化简，随后证明均方尾部界及极限交换。没有把这些整数平均结论替换成任何素数子集上的相关结论。

其他尚未完成的分析层内容：

- 三进对数 L(n)=log₃-ad U(n) 的收敛、同态性与等距性。当前只形式化其前置的整数坐标 U。
- 限制素数乘子的精确升层密度。需要素数在固定等差数列中的渐近计数；有限余数计算不代替它。
- 文献层的素数单点分布和连续素数同值段仍需相应渐近/连续素数理论的可审计形式化。

这些未完成项没有放进默认 import 中成为公理，也没有用假设同名结论来制造“已证明”的表象。

## 4. 核验与复现

固定的 Lean 4.34.0 和 mathlib 修订不变。完整核验：

```sh
python3 scripts/verify.py
```

包括库构建、三组 Lean 回归模块、全部 `#print axioms`、源码禁用项检查、新增的审计覆盖检查及原有 Python 检查。`check_audit_coverage.py` 要求每条项目 theorem/lemma 在审计表中恰好出现一次；它不取代实际内核公理审计。

`F3CorrelationFinite.lean` 复用固定 mathlib 的 `Mathlib/Data/Int/CardIntervalMod.lean`（完整区间中的模类计数）和 `Nat.ModEq.of_dvd`。截至本轮已验证代码 head `e9563d557e3e95603b3aad5b264b52dea7329698`：Lean CI #80 构建、回归、公理、源码、覆盖、有限检查均通过；212 条项目 theorem/lemma 全部审计，只使用标准 Lean 公理。文档更新后的最终 head 仍以其后续 CI 为准。

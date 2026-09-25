# 质因数和左右平衡：Lean 形式化地图

本页记录第二、三轮研究笔记中已经写成 Lean 声明的部分。是否通过核验，以本提交的完整 `Lean` 工作流、`#print axioms` 输出及覆盖检查为准。条件性结论的输入必须显式出现在定理类型中。

## 1. 不同统计量分别命名

| Lean 定义 | 数学含义 |
|---|---|
| `bigOmega n` | 质因数计重个数 Ω(n) |
| `omegaSum n` | Ω(n−1)+Ω(n+1)，沿用原有含义 |
| `primeFactorSum n` | 质因数计重求和 S(n) |
| `primeFactorSumDiff n` | 整数差 S(n+1)−S(n−1) |
| `primeFactorDefect n` | 整数差 n−S(n) |
| `IsPrimeFactorSumBalancedPrime p` | p 为素数且左右 S 相等 |
| `IsDoubleBalancedPrime p k` | p 为素数、左右 S 相等且左右 Ω 均为 k |

`primeFactorSum` 使用 `n.primeFactorsList.sum`；不替换已有 Ω 或 F₃ 接口。所有差分先把每个项转成整数再相减。S(0)=0 是 mathlib 的全函数约定；乘法定理保留两个因子非零的前提。

## 2. 模块与主要声明

| 模块 | 主结果 |
|---|---|
| [FactorSum](../../OmegaBalance/FactorSum.lean) | S(ab)=S(a)+S(b)、S(q^k)=kq、因子表证书接口、平衡零点刻画、约去共同因子 2、一般余因子构造与缺陷公式 |
| [FactorSumArithmetic](../../OmegaBalance/FactorSumArithmetic.lean) | S(n)≤n；正整数等号当且仅当素数或 4；奇合数的 3S(n)≤n+9；S 与 Ω、v₂ 的奇偶关系；双平衡的模 8 限制 |
| [FactorSumFamily](../../OmegaBalance/FactorSumFamily.lean) | 五表达式素性前提下的求和平衡、左右 Ω 为 5 与 4、精确缺陷等价；余因子反解和五级因数对恒等式 |
| [FactorSumStructure](../../OmegaBalance/FactorSumStructure.lean) | 双平衡的邻数形状、共同级数至少 5、五级因子证书的充分性和模 48 限制 |
| [FactorSumFive](../../OmegaBalance/FactorSumFive.lean) | 五级形状的必要性与充要分类；五级双平衡不能成孪生对；双平衡孪生的共同级数至少 6 |
| [FactorSumLowAux](../../OmegaBalance/FactorSumLowAux.lean) | 低总计数分类所需的约分、奇偶、整除和间距引理 |
| [FactorSumSmallCertificates](../../OmegaBalance/FactorSumSmallCertificates.lean) | 小于 2000 的完整素数目录及左右分解证书，由 Lean 内核验证，而不是读取外部扫描结果 |
| [FactorSumLowCount](../../OmegaBalance/FactorSumLowCount.lean) | 对任意输入证明小级数中心小于 2000，接上有限证书得到完整分类；固定总计数的无穷性下界与显式前提下的参数族传递 |
| [FactorSumExamples](../../OmegaBalance/FactorSumExamples.lean) | 11、17、31、3615811 及两个五级双平衡大素数的内核回归；最小可达共同级数恰为 5 |

## 3. 五项同时为素数的定理

定义自然数参数多项式：

$$
\begin{aligned}
U(t)&=2t+1, & V(t)&=15t+8,\\
Q(t)&=390t^2+238t+17, & R(t)&=390t^2+225t+16,\\
P(t)&=23400t^3+25980t^2+8160t+511.
\end{aligned}
$$

`SumFamilyPrimeValues t` 只记录五个素性前提。主要接口为：

```lean
import OmegaBalance
open OmegaBalance

example {t : ℕ} (h : SumFamilyPrimeValues t) :
    IsPrimeFactorSumBalancedPrime (sumFamilyCenter t) :=
  sumFamily_five_primes h

example {t : ℕ} (h : SumFamilyPrimeValues t) :
    omegaSum (sumFamilyCenter t) = 9 :=
  sumFamily_omegaSum_eq_nine h
```

代数恒等式不需要素性；只需 U、V、Q、R 为素数，就能证明两邻数求和平衡。第五项 P 的素性专门保证中心是素数。主定理没有声称五项能同时为素数无穷多次。

左右质因数计数分别为 5、4，故 `sumFamily_omegaDiff_eq_neg_one` 给出 Ω 差为 −1。这个族不是 Ω 平衡或双平衡族。

保留 U、V 为素数、允许 Q、R 为合数时：

$$
F_\Sigma(P(t))=D(Q(t))-D(R(t)),\qquad D(n)=n-S(n).
$$

这是 `sumFamily_defect_identity`；`sumFamily_balanced_iff_defect` 给出平衡与缺陷相等的充要条件。不声称放宽后的集合已经找到额外解。

一般余因子反解保留 Pomerance 的来源，见 [第二轮笔记](research_round2.md)；不宣称原公式首创。

## 4. 两个完整的结构分类

### 低总计数

`sumBalanced_total_le_eight_iff` 对每个自然数 p 给出：

$$
\bigl(p\text{ 为 }S\text{-平衡素数且 }T_\Omega(p)\le8\bigr)
\iff p\in\{11,17,31\}.
$$

它不是仅在有限区间内成立的定理。证明先由任意输入推出 `p < 2000`（`sumBalanced_low_count_bound`），再使用有限内核证书完成分类。证书验证包含目录完整性、每个因子的素性、乘积、总和与个数；篡改或遗漏证书会导致编译失败。

除三个例外外，总计数至少为 9。相应地，若某个固定总计数层包含无穷多个求和平衡素数，则该总计数至少为 9。

### 五级双平衡

`doubleBalanced_five_shape_iff` 在 p 为素数的前提下，给出五级双平衡与以下形状的等价：

$$
\{p-1,p+1\}=\{6bcd,8rs\},\qquad r+s+1=b+c+d,
$$

其中 b,c,d,r,s 全为奇素数，允许同一侧重复出现相同素因子，左右方向由析取保留。

由此推出 p≡7 或 41 (mod 48)，以及两个五级双平衡素数不能互为孪生。一般双平衡孪生对由共享邻数强制同级，且这个级数至少为 6。定理只给必要限制，不声称这样的孪生对存在。

## 5. 最小可达共同级数

`doubleBalanced_level_ge_five` 不依赖上面的低总计数分类，直接由模 8 和因子形状证明共同级数至少为 5。

`doubleBalanced_870404071` 与 `doubleBalanced_748465063` 则给出真正达到 5 的实例；中心与各因子的素性均由 Lean 证明，没有把 Python 素性测试作为假设。于是：

```lean
import OmegaBalance.FactorSumExamples
open OmegaBalance

example :
    (∃ p : ℕ, IsDoubleBalancedPrime p 5) ∧
      ∀ p k : ℕ, IsDoubleBalancedPrime p k → 5 ≤ k :=
  doubleBalanced_minimum_level
```

这里是最小**级数**，不是最小**素数**。不声称这两个具体素数是该层的最小元素。

## 6. 无穷性与尚未形式化的边界

`infinite_sumFamily_implies_level_nine` 的类型明确要求五项素数参数集合无限，然后利用中心多项式的严格单调性，将该前提传递成总计数 9 层无限。它没有证明输入前提，也没有把 Schinzel 假设 H 加为公理。

以下仍保留为研究笔记或程序结果，不在 Lean 已证结果中冒充完成：

- 从 Schinzel 假设 H 到本族无穷参数的完整多项式不可约性、无固定素因子验证与假设 H 接口；
- Pomerance 计数上界、零相对密度与倒数和收敛的解析证明；
- 两个十九位中心的 Python Pocklington 证书向 Lean 的移植。

原有 Ω 平衡哥德巴赫猜想仍只是猜想，没有加入证明依赖。

## 7. 核验与审计

复用仓库固定 Lean/mathlib 版本，执行：

```sh
python3 scripts/verify.py
```

完整检查包括库编译、原有三组回归及新增 `FactorSumExamples`、所有声明的公理输出、源码保护、审计覆盖与原有 F₃ 有限回归。

有限证书中的 `decide +kernel` 要求内核归约并验证证明项；不是 `native_decide` 或 `+native`。公理白名单仍仅为 `propext`、`Classical.choice`、`Quot.sound`。

`Factor-sum verification` 工作流继续独立复核 Python 参数族结果；它不能替代上述 Lean 编译及公理审计。

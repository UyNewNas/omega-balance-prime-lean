# Ω-balanced primes in Lean

按重数计数的 Ω 平衡素数，以及素数相邻整数的三进赋值差分。

**Ω 不是不计重数的 ω；`omegaDiff` 不是 `f3`。所有差分先转为整数再相减。**

## 定义

令 Ω(n) 为 `n.primeFactorsList.length`，即质因数总个数（按重数计）。

- `IsOmegaBalancedPrime p`：`p` 是素数，且 Ω(p−1) = Ω(p+1)。
- `omegaDiff p : ℤ`：Ω(p+1) − Ω(p−1)。
- `omegaSum p : ℕ`：Ω(p−1) + Ω(p+1)。
- `v3 n : ℕ`：`n.factorization 3`。
- `f3 p : ℤ`：v₃(p+1) − v₃(p−1)。

`valuation q n` 和 `valuationDiff q n` 提供一般素数 q 的接口。
`neighborDiff f n` 统一表达各种右减左统计量。

## 主定理：孪生素数的精确反号

```lean
import OmegaBalance
open OmegaBalance

example {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    f3 (p + 2) = -f3 p ∧ f3 p ≠ 0 ∧ f3 (p + 2) ≠ 0 :=
  f3_twin hp hq h3
```

不只是变号，还有：

```math
F_3(p)=v_3(p+1)>0,\qquad F_3(p+2)=-v_3(p+1)<0.
```

因此绝对值相等，乘积严格小于零。接口分别是
`f3_twin_values`、`f3_twin_signs`、`f3_twin_abs_eq` 和 `f3_twin_mul_neg`。

证明先用素数性得到 p ≡ 2 (mod 3)，再证明两个外侧邻数不被 3 整除、
共享的中间邻数被 3 整除。更强的算术核心 `f3_opposite_of_mod_three`
只需 n > 1 且 n ≡ 2 (mod 3)，不需要素数性。

## 其他基本接口

| 接口 | 内容 |
|---|---|
| `omegaDiff_eq_zero_iff` | Ω 差分为零当且仅当邻数 Ω 平衡 |
| `isOmegaBalancedPrime_iff` | 平衡素数等价于素数且 Ω 差分为零 |
| `neighborDiff_pos_iff`, `neighborDiff_neg_iff` | 差分符号与左右计数大小关系 |
| `bigOmega_mul` | 非零 a,b 满足 Ω(ab) = Ω(a)+Ω(b) |
| `bigOmega_prime_pow` | 素数幂满足 Ω(qᵏ) = k |
| `omegaDiff_prime_eq_half_diff` | 奇素数两侧的公共因子 2 可以约去 |
| `isOmegaBalanced_iff_half` | 约去公共因子 2 后的平衡判据 |
| `omegaSum_eq_bigOmega_sq_sub_one` | n > 1 时 S(n) = Ω(n²−1) |
| `omegaSum_add_omegaDiff`, `omegaSum_sub_omegaDiff` | S±F 分别是右、左计数的两倍 |
| `valuation_eq_padicValNat` | 素数底数时与 mathlib 的 `padicValNat` 对接 |
| `f3_ne_zero_of_prime` | p > 3 的素数均满足 F₃(p) ≠ 0 |
| `f3_pos_iff_mod_three`, `f3_neg_iff_mod_three` | 正、负分别对应模 3 余 2、余 1 |
| `twin_mod_six`, `twin_six_mul_form` | 非例外孪生素数的模 6 与 6k±1 形式 |

完整定义与证明在 `OmegaBalance/Basic.lean`、`Valuation.lean` 和 `F3.lean`。
`Examples.lean` 包含具体数值与反例回归证明；它不作为主库的默认 import。

## 必须保留的边界

`bigOmega 0 = 0`、`v3 0 = 0` 是 mathlib 的全函数约定，**不是说零具有有限的通常赋值**。
非零假设不能从乘法性、赋值正性等定理中删除。`n - 1` 在自然数中是截断减法；
使用邻数作为正整数的定理均明确限制 n > 1 或相应素数范围。

`p > 3` 不能删除：孪生对 (3,5) 满足 F₃(3)=0、F₃(5)=1。

反号也不是孪生的充分条件：F₃(5)=1、F₃(13)=−1，但 13−5=8。
同样，F₃ 的定理不能移植成完整 Ω 差分的定理：Ω 差分在 (5,7) 上分别是 0、1。
这些都在 `Examples.lean` 中作为回归目标。

本仓库不把“无穷多平衡素数”“无穷多孪生素数”或任何有界间距断言作为前提或已证结果。

## 构建与核验

Lean **4.34.0**；mathlib **v4.34.0**，固定到提交
`5ed2965256430c3649e86755f9576b54eca72435`。安装 elan 后：

```sh
lake update
lake exe cache get
lake build
lake build OmegaBalance.Examples
python3 scripts/verify.py
```

`verify.py` 重跑库构建、回归证明、公理审计与源码检查，并保存日志。
Windows 可使用 `python scripts/verify.py`。

GitHub Actions 的 `Lean` 工作流执行相同的四层检查并保存日志。
`#print axioms` 覆盖当前全部 **78** 条 theorem 声明（包括回归证明），
仅允许 `propext`、`Classical.choice`、`Quot.sound`。
源码检查禁止证明占位、自定义公理、unsafe 证明路径和原生决定过程逃逸。

**源码扫描通过不等于 Lean 编译通过。是否完成内核核验，以对应提交的 CI 和公理日志为准。**

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

## 质因数和相加平衡：研究证明与精确计算

新增 [第二轮完整研究笔记](docs/sum_balance/research_round2.md)。这里
`S(n)` 是质因数计重求和，研究 `S(p-1)=S(p+1)`；它**不是**上面的 `omegaSum`。

笔记收录参数族的平衡证明、所有素数模数的局部相容性、不可约性、
**Schinzel 假设 H 下**的条件性无穷结论、Pomerance 已有定理给出的稀疏性推论，
以及允许二次表达式为合数时的缺陷恒等式 `F(P)=D(q)-D(r)`。
已有构造公式的来源明确归于 Pomerance 式（3），不宣称首创。

本次完整复现 `1 <= t <= 50000`：48 个四项素数候选、3 个有素性证书的中心，
参数为 `5, 41529, 48465`。范围只针对该参数族，不是全体相加平衡素数。

| 文件 | 用途 |
|---|---|
| [研究笔记](docs/sum_balance/research_round2.md) | 完整数学证明、前提、来源和形式化状态 |
| [验证脚本](scripts/verify_sum_balance_family.py) | 标准库扫描、完整试除、Pocklington 证书与回归比较 |
| [精确结果](data/sum_balance/family_1_50000.json) | 三个中心的分解、质因数和及证书 |
| [独立工作流](.github/workflows/sum-balance.yml) | 每次 push/PR 重算并比对已提交报告 |

从仓库根目录执行：

```sh
python3 scripts/verify_sum_balance_family.py --limit 50000 --output sum_balance_family_actual.json --check-against data/sum_balance/family_1_50000.json
```

Windows 可使用 `python`。不要使用 `-O`，避免禁用审计断言。

**这次新增内容尚未转为 Lean 定理。** 现有 Lean 文件、78 条 theorem 的审计、
工具链和原 CI 均保持不变；这里的假设 H 不进入 Lean 公理。
Python 数值/素性验证通过，不等于完成了新结论的 Lean 内核核验。

# F₃ 精确层级素数无穷性与双向连续变号

本轮实现对应全量清单 [INF-1、INF-2](f3_formalization_tasks.md)。固定 Lean/mathlib，不用额外数论公理。验证状态与精确提交见任务清单及 PR #6。

## 1. 精确层级的无穷性

F₃(n)=v₃(n+1)-v₃(n-1)，差在整数中计算。

对每个 k≥1，取模数 M=3^(k+1) 与两个互素余数

- a₊=3^k-1；
- a₋=3^k+1。

若 n≡a₊ (mod M)，则 n+1=3^k(1+3t)，从而 F₃(n)=k。
若 n≡a₋ (mod M)，则 n-1=3^k(1+3t)，从而 F₃(n)=-k。
这里 n>1，且 t 是除以M的商；这是精确赋值，不是仅整除。

由 mathlib 已证 Dirichlet 定理，每个这类余数都有超过任意界限的素数，因此

```lean
f3_prime_level_infinite {c : ℤ} (hc : c ≠ 0) :
  {p : ℕ | p.Prime ∧ 3 < p ∧ f3 p = c}.Infinite
```

注意：上述每侧只选择了一个足以证明无穷性的余数类。精确+k实际上有两个模M余数类；本轮没有给出密度。p=17满足F₃=2，但不属于模27余8的所选类，已有回归证明。

## 2. 真正连续素数的无穷变号

```lean
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧
    ∀ r : ℕ, p < r → r < q → ¬ r.Prime
```

给定足够大的正号素数a，取a之后第一个负号素数q，再取q之前最大的素数p。
若p=a则其为正号；若p>a且为负号，就与q的最小性冲突。
因为大于3的素数不取零值，p必为正号，且p,q在完整素数数列中相邻。
负→正使用同一构造，把F₃乘以-1。

这不是先筛出某符号子序列再讲相邻。分别得到两种转移的无限左端点集合，以及

```lean
f3_consecutive_sign_changes_infinite :
  {p : ℕ | 3 < p ∧ ∃ q, ConsecutivePrimes p q ∧ f3 p * f3 q < 0}.Infinite
```

没有相等绝对值、固定间距、素数密度或连续同值长串藏在结论里；(7,11) 的内核回归明确保留为非孪生的连续异号对。

## 3. 接口地图

| 接口 | 含义 |
|---|---|
| f3_pos_residue_coprime / f3_neg_residue_coprime | 所选余数类的互素性 |
| f3_pos_of_modEq_level / f3_neg_of_modEq_level | 余数类到精确层级 |
| exists_prime_gt_f3_pos / exists_prime_gt_f3_neg | 任意界限之外的精确层级素数 |
| f3_prime_level_pos_infinite / f3_prime_level_neg_infinite | 正负层级的集合无穷性 |
| f3_prime_level_infinite | 合并为任意c≠0 |
| f3_prime_zero_level_empty | 零层例外 |
| exists_ordered_prime_opposite_levels | 有序相反层级存在，但不约束距离 |
| f3_crossing_after_prime | 从一个符号走到另一个符号的连续跨越构造 |
| exists_consecutive_primes_f3_pos_neg / exists_consecutive_primes_f3_neg_pos | 任意大处出现两个方向的连续跨越 |
| f3_consecutive_pos_neg_infinite / f3_consecutive_neg_pos_infinite | 两个方向各自的无穷性 |
| f3_consecutive_sign_changes_infinite | F₃乘积为负的连续跨越无限 |

## 4. 来源与信任

复用固定 mathlib 提交 `5ed2965256430c3649e86755f9576b54eca72435` 中
`Mathlib/NumberTheory/LSeries/PrimesInAP.lean` 的
`Nat.forall_exists_prime_gt_and_modEq`。其证明链经整数/ZMod包装器回到
`Nat.infinite_setOfPred_prime_and_eq_mod`，不是在本项目中假设 Dirichlet 定理。

所有公开定理均登记 scripts/Audit.lean，使用原有源码和公理白名单检查。
任何测试运行是否通过，以精确head的CI为准。全量任务的相关核、三进对数、渐近密度与同值长串并未在本轮完成。

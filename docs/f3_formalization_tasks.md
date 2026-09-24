# F₃ 全量形式化任务清单

此文件是持续推进的权威任务账本。只有精确提交实际通过 Lean 构建、回归、公理、源码与声明覆盖门禁的结果才标记为完成；纸面推导、Python 有限验算或外部文献本身不算 Lean 证明。

## 固定边界

- namespace：`OmegaBalance`。
- Lean 4.34.0；mathlib 固定提交 `5ed2965256430c3649e86755f9576b54eca72435`。
- 每条项目 `theorem` / `lemma` 必须在 `scripts/Audit.lean` 恰好登记一次。
- 禁止 `sorry` / `admit`、自定义数学公理、unsafe/native proof escape、同名假设伪装结论或削弱前提。
- PR #5 是独立的质因数求和研究线；F₃ 推进不覆盖其分支。
- 最终状态以精确 GitHub Actions head 或相同 Git tree 的成功门禁为准；运行中的 CI 不登记为通过。

## 总目标

| ID | 目标 | 状态 |
|---|---|---|
| INF-1 | 每个固定 `k≥1`，`F₃=+k`、`F₃=-k` 的素数各无穷多 | **完成，PR #6** |
| INF-2 | 全体素数数列中连续两项的正→负、负→正转移各无穷次 | **完成，PR #6** |
| COR-1 | 固定 `h≥0` 的完整整数相关核 | **进行中** |
| COR-2 | 固定 `r≥1` 的均方近似周期 `4/3^r` | 未完成；依赖 COR-1 |
| DEN-1 | 素数单点比例 `3^(-k)`、层级尾部 `3^(1-K)` | 未完成；需 ANT 等差数列渐近计数桥梁 |
| DEN-2 | 固定乘子升层密度；含乘数 17 的 `1/2,1/3,1/9,…` 条件分布 | 未完成；依赖 DEN-1 |
| LOG-1 | 真正 `log₃-ad U` 的收敛、同态、等距及 F₃ 连接 | 未完成；已有整数坐标 U |
| RUN-1 | 任意固定 `c≠0,L≥1` 的连续素数同值长串 | 未完成；需 Shiu / BFTB 的可审计形式化 |
| RUN-2 | 上述长串的跨度有界版本 | 未完成；依赖定量上游版本 |

## INF-1 / INF-2：已完成

PR #6 合入主分支 `007da90defc99dcf9fb92aad43a9d684ff99cb0b`。核心接口：

- `f3_prime_level_infinite`：任意 `c : ℤ`、`c ≠ 0`，集合 `{p | p.Prime ∧ 3 < p ∧ f3 p = c}` 无限；
- `exists_prime_gt_f3_pos` / `exists_prime_gt_f3_neg`：超过任意界限的精确 `±k` 素数；
- `f3_prime_zero_level_empty`：`p>3` 的素数没有零层；
- `f3_consecutive_pos_neg_infinite` / `f3_consecutive_neg_pos_infinite`：真正连续素数的两种符号转移分别无限。

复用锁定 mathlib 的 `Nat.forall_exists_prime_gt_and_modEq` / `Nat.infinite_setOfPred_prime_and_eq_mod`；没有推出固定间距、等幅或孪生无穷性。

## COR-1：已经完成并合入的链条

1. **完整周期余数重叠**：`F3CorrelationFinite.lean`，精确计数两个幂三余数类在 `0≤n<3^R` 内的交集。
2. **单层有符号相关核**：`F3CorrelationLayer.lean`，将四个重叠数合并为三个模条件。
3. **完整周期展开**：`F3CorrelationPeriod.lean`，得到截断相关的有限双重和。
4. **几何权重**：`F3CorrelationWeight.lean`，证明 `W_R(d)=3^R-3^(R-min(R,d))-min(R,d)`。
5. **capped depth 与零边界**：`F3CorrelationDepth.lean`，保留 `v₃,R(0)=R`，并用 `Nat.dist h 2` 统一处理 `h<2,h=2,h>2`。
6. **完整周期闭式**：`F3CorrelationClosed.lean`，得到三个几何项加三个深度边界项的精确公式；含 `h=0`、`h=2` 两个独立边界。
7. **归一化完整周期 cutoff 极限**：`F3CorrelationLimit.lean`，证明 `S_R(h)/3^R → |h-2|₃+|h+2|₃-2|h|₃`，其中零点三进核显式取 0。
8. **任意长度 quotient/remainder 分解**：`F3CorrelationCesaro.lean`，PR #13 已合入主分支 `f2a4f7595e5ee9d355d2d621438032121fc27dfe`。证明固定 `R` 时相关 summand 的周期性、任意部分和的完整块+终端块精确分解，以及终端块统一界 `≤3^R R²`。

PR #13 的最终验证确认 library build、三组 kernel regressions、公理审计、源码审计、声明一对一覆盖、144,240 项既有有限检查及 11 组边界测试全部通过。

## COR-1 当前推进：固定 cutoff 的任意长度 Cesàro 极限（PR #14）

分支 `feat/f3-correlation-cesaro-limit` 新增 `OmegaBalance/F3CorrelationCesaroLimit.lean`。目标是对每个固定 `R,h` 证明

```text
(1/N) * sum_{n<N} F_{3,R}^{per}(n) F_{3,R}^{per}(n+h)
    → f3PeriodicCorrelationAverage R h.
```

当前写入的证明结构：

- `f3PeriodicCorrelationCesaroAverage`：任意长度的实值归一化平均；
- `f3PeriodicCorrelationCesaroAverage_eq`：把平均精确改写为“完整周期平均 × (1 - (N mod 3^R)/N) + 终端块/N”；
- `tendsto_f3PeriodicCorrelationRemainder_div`：由 PR #13 的统一终端块界和 `tendsto_bdd_div_atTop_nhds_zero` 得到终端块/N→0；
- `tendsto_f3PeriodicCorrelationCesaroAverage`：复用 mathlib 的 `tendsto_mod_div_atTop_nhds_zero_nat` 收掉 `(N mod 3^R)/N→0`，得到固定 cutoff 的任意长度 Cesàro 极限。

这些声明已经加入 `scripts/Audit.lean`，但 **只有 PR #14 最终精确 head 的完整 CI 成功后才把本阶段改成“完成”**。不得把固定 cutoff 极限冒充原始 `F₃` 的无限相关核。

## COR-1 剩余链条

PR #14 完成后仍需：

1. 证明 `F₃-F₃,R` 的 `L²` Cesàro 尾部界，目标量级 `O(3^(1-R))`，并明确自然减法边界与周期版本的连接。
2. 用 Cauchy–Schwarz 控制原始相关平均与固定 cutoff 相关平均之间的误差。
3. 完成 cutoff 极限与 Cesàro 极限交换，得到原始 `F₃` 的无限相关核
   `|h-2|₃+|h+2|₃-2|h|₃`。
4. 从 COR-1 推导 COR-2：固定 `r≥1` 的均方近似周期 `4/3^r`；`r=0` 必须单独处理，不能套该简式。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

## 停止规则

只有 INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，上游依赖经过信任审计，且精确版本的构建、回归、公理、源码、覆盖全部通过后，才结束全量任务。当前尚未满足停止条件。

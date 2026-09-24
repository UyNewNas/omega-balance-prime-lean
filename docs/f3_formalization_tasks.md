# F₃ 全量形式化任务清单

此清单是周期推进的持久化状态。只有精确提交实际通过 Lean 内核、源码与公理审计的结果才登记为完成；纸面推导、有限计算或外部文献本身不替代 Lean 证明。

## 固定边界

- namespace：`OmegaBalance`。
- Lean 4.34.0；mathlib 固定提交 `5ed2965256430c3649e86755f9576b54eca72435`。
- 所有新增 theorem/lemma 均需进入 `scripts/Audit.lean`，且 `scripts/check_audit_coverage.py` 一对一覆盖。
- 禁止 `sorry` / `admit`、自定义数学公理、unsafe/native proof escape、同名假设伪装结论。
- PR #5 是独立的质因数求和研究线；F₃ 推进不覆盖其分支。
- 本地没有固定 Lean 工具链可供可信核验；最终状态以精确 GitHub Actions head/相同文件树为准。

## 总目标

| ID | 目标与前提 | 当前实现/依赖 | 状态 |
|---|---|---|---|
| INF-1 | 每个固定 `k≥1`，`F₃=±k` 的素数各有无穷多个 | `F3Infinitude.lean`；固定 mathlib 的 Dirichlet 定理 | **已完成并合入，PR #6** |
| INF-2 | 全体素数数列中连续两项的正→负、负→正转移各无穷次 | `F3SignChanges.lean`；显式 `ConsecutivePrimes` | **已完成并合入，PR #6** |
| COR-1 | 固定 `h≥0` 的完整整数相关核 | `F3Finite` + `F3CorrelationFinite/Layer/Period/Weight`；有限周期展开持续推进 | **进行中** |
| COR-2 | 固定 `r≥1` 的均方近似周期 `4/3^r` | 依赖 COR-1；`r=0` 不能套该简式 | 未完成 |
| DEN-1 | 素数单点比例 `3^(-k)`、层级尾部 `3^(1-K)` | 需核验 ANT `WeakPNT_AP` 与加权→素数计数桥梁 | 未完成 |
| DEN-2 | 固定乘子升层密度；含乘数17的 `1/2,1/3,1/9,…` 条件分布 | DEN-1 + 有限余数类计算 | 未完成 |
| LOG-1 | 真正 `log₃-ad U` 的收敛、同态、等距及 F₃ 连接 | 已有整数坐标 U；需三进分析接口 | 未完成 |
| RUN-1 | 任意固定 `c≠0,L≥1` 的连续素数同值长串 | Shiu / Banks–Freiberg–Turnage-Butterbaugh；需可审计形式化 | 未完成 |
| RUN-2 | 上述长串的跨度有界版本 | RUN-1 的定量上游版本 | 未完成 |

## 已完成：INF-1 / INF-2

工作分支 `feat/f3-infinitude-sign-changes`，PR #6，合入主分支提交 `007da90defc99dcf9fb92aad43a9d684ff99cb0b`。

核心接口：

- `f3_prime_level_infinite`：任意整数 `c ≠ 0`，集合 `{p : p.Prime ∧ 3 < p ∧ f3 p = c}` 无限。
- `exists_prime_gt_f3_pos/neg`：任意界限与 `k≥1`，存在超过该界限且取精确 `±k` 的素数。
- `f3_prime_zero_level_empty`：大于3的素数没有零层。
- `f3_consecutive_pos_neg_infinite` / `f3_consecutive_neg_pos_infinite`：真正连续素数的两种符号转移分别无限。
- `f3_consecutive_sign_changes_infinite`：连续素数中 `F₃` 乘积为负发生无穷多次。

复用锁定 mathlib 的 `Nat.forall_exists_prime_gt_and_modEq` / `Nat.infinite_setOfPred_prime_and_eq_mod`；没有把无穷性升级为固定间距、等幅或孪生结论。

精确验证：PR head `01a83e1787dea405514e660059a4d066f9861ce8`，Lean CI #72、Factor-sum #60 成功；当时 209 条声明公理与覆盖审计全部通过。

## COR-1 已完成的有限基础层

### A. 完整周期幂三余数重叠

`OmegaBalance/F3CorrelationFinite.lean` 已证明：

- 单个模 `3^k` 余数类在完整 `3^R` 周期中出现 `3^(R-k)` 次；
- 两个嵌套幂三余数类的精确交集计数 `modPairCount_eq`；
- 平移后的计数 `modShiftPairCount_eq`；
- 四种正/负层目标分别化为 `h≡0`、`h≡2`、`h+2≡0` 的兼容条件。

### B. 单层有符号相关核

`OmegaBalance/F3CorrelationLayer.lean` 的 `f3LayerCorrelation_eq` 将四个重叠数合并为

```text
2·1[h≡0 mod 3^min] - 1[h≡2 mod 3^min] - 1[h+2≡0 mod 3^min]
```

乘以完整周期权重 `3^(R-max)`。这一层仍是有限计数，不含无限平均。

主分支提交 `b4a5dbb5b0dd4c1edc940b0a0acdee867620ce22` 记录了上述平移/单层核推进；其来源 PR head `661f160b788bdfd8ab189ab4953b8592362f8db8` 已由 Lean CI #122、Factor-sum #110 验证。

### C. 完整周期展开（PR #9，已合入）

新增 `OmegaBalance/F3CorrelationPeriod.lean`：

- `f3PeriodicTrunc`：用周期余数层表示的截断函数；
- `f3PeriodicTrunc_eq_f3Trunc`：在 `n>1` 上与原 `f3Trunc` 精确一致，保留自然数减法边界；
- `sum_f3ModIndicator_mul_shift`、`sum_f3ResidueLayer_mul_shift`：把周期和化为平移重叠计数；
- `f3PeriodicCorrelationSum_eq_layer_sum`：完整 `3^R` 周期相关和展开成双层 `f3LayerCorrelation`；
- `f3PeriodicCorrelationSum_eq_explicit`：进一步代入 `h≡0`、`h≡2`、`h+2≡0` 的三类兼容条件。

PR #9 最终 head `2669ff93ad750b81ce21d87e8f4997eb5c79fb04` 的 Lean CI #138 与 Factor-sum #126 均成功；随后 squash 合入主分支 `37da64866c5ae30c51ee9fc9c49e89eed92b125e`。没有在该 PR 中声称无限相关极限或尾部交换。

## 当前工作：有限几何权重闭式（PR #10）

工作分支 `feat/f3-correlation-geometric-weight`，PR #10。

新增 `OmegaBalance/F3CorrelationWeight.lean`，抽离双层和中只依赖层深与 `min/max` 的权重

```math
W_R(d)=\sum_{j,k=1}^{R}\mathbf 1_{\min(j,k)\le d}\,3^{R-\max(j,k)}.
```

当前实现目标：

- `f3CorrelationWeight_succ`：
  ```math
  W_{R+1}(d)=3W_R(d)+2\min(R,d)+\mathbf1_{R+1\le d};
  ```
- `f3CorrelationWeight_eq`：
  ```math
  W_R(d)=3^R-3^{R-\min(R,d)}-\min(R,d).
  ```

首个 CI #144 暴露的是 Lean 规范化/展开问题，而非公式反例：`simp` 将 `min/max` 的 `j+1,k+1` 形态改写后未闭合，并且递推末尾过度展开 `f3CorrelationWeight`。已改为显式 `if_pos/if_neg`、受控 `change` 与不展开 RHS 的证明。最终 head 仍须重新通过完整门禁后才能登记为完成并合入。

## COR-1 下一阶段

在 `f3CorrelationWeight_eq` 通过后，下一步不是直接跳到无限极限，而是完成以下桥梁：

1. 定义保留 `v₃,R(0)=R` 边界约定的自然数 capped depth，使 `m≤R` 时
   `3^m ∣ n ↔ m ≤ cappedDepth R n`；不能用 mathlib 总化的 `v₃(0)=0` 代替。
2. 对交叉项用 `Nat.dist h 2` 表示 `h≡2`：证明
   `h ≡ 2 [MOD 3^m] ↔ 3^m ∣ Nat.dist h 2`，从而统一 `h<2,h=2,h>2` 三个边界。
3. 将 `f3PeriodicCorrelationSum_eq_explicit` 精确重写成三个闭式权重：
   `2·W_R(depth(h)) - W_R(depth(|h-2|)) - W_R(depth(h+2))`。
4. 再处理归一化完整周期极限、任意 Cesàro 长度的周期余项、`L²` 截断尾部界与极限交换，最终得到原始 `F₃` 的无限相关核。
5. COR-1 完成后，用相关核推导 COR-2；`r=0` 仍单独处理。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

停止规则：INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，且精确版本构建、回归、公理、源码与覆盖门禁全部通过后，才结束全量任务；当前仍不满足停止条件。

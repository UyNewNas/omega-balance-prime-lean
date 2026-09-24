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
| COR-1 | 固定 `h≥0` 的完整整数相关核 | `F3Finite` + `F3CorrelationFinite/Layer/Period/Weight/Depth/Closed`；有限周期闭式已到位，仍缺极限与尾部交换 | **进行中** |
| COR-2 | 固定 `r≥1` 的均方近似周期 `4/3^r` | 依赖 COR-1；`r=0` 不能套该简式 | 未完成 |
| DEN-1 | 素数单点比例 `3^(-k)`、层级尾部 `3^(1-K)` | 需核验 ANT `WeakPNT_AP` 与加权→素数计数桥梁 | 未完成 |
| DEN-2 | 固定乘子升层密度；含乘数17的 `1/2,1/3,1/9,…` 条件分布 | DEN-1 + 有限余数类计算 | 未完成 |
| LOG-1 | 真正 `log₃-ad U` 的收敛、同态、等距及 F₃ 连接 | 已有整数坐标 U；需三进分析接口 | 未完成 |
| RUN-1 | 任意固定 `c≠0,L≥1` 的连续素数同值长串 | Shiu / Banks–Freiberg–Turnage-Butterbaugh；需可审计形式化 | 未完成 |
| RUN-2 | 上述长串的跨度有界版本 | RUN-1 的定量上游版本 | 未完成 |

## 已完成：INF-1 / INF-2

PR #6 已合入主分支提交 `007da90defc99dcf9fb92aad43a9d684ff99cb0b`。核心接口包括：

- `f3_prime_level_infinite`：任意整数 `c ≠ 0`，集合 `{p : p.Prime ∧ 3 < p ∧ f3 p = c}` 无限；
- `exists_prime_gt_f3_pos/neg`：任意界限与 `k≥1`，存在超过该界限且取精确 `±k` 的素数；
- `f3_prime_zero_level_empty`：大于3的素数没有零层；
- `f3_consecutive_pos_neg_infinite` / `f3_consecutive_neg_pos_infinite`：真正连续素数的两种符号转移分别无限；
- `f3_consecutive_sign_changes_infinite`：连续素数中 `F₃` 乘积为负发生无穷多次。

复用锁定 mathlib 的 `Nat.forall_exists_prime_gt_and_modEq` / `Nat.infinite_setOfPred_prime_and_eq_mod`；没有把无穷性升级为固定间距、等幅或孪生结论。PR head `01a83e1787dea405514e660059a4d066f9861ce8` 的 Lean CI #72、Factor-sum #60 成功；当时 209 条声明公理与覆盖审计全部通过。

## COR-1 已完成的有限层

### A. 完整周期幂三余数重叠

`OmegaBalance/F3CorrelationFinite.lean` 已证明单余数类计数、两个嵌套幂三余数类的精确交集 `modPairCount_eq`、平移计数 `modShiftPairCount_eq`，以及四种正/负层目标分别化为 `h≡0`、`h≡2`、`h+2≡0` 的兼容条件。

### B. 单层有符号相关核

`OmegaBalance/F3CorrelationLayer.lean` 的 `f3LayerCorrelation_eq` 将四个重叠数合并为

```text
2·1[h≡0 mod 3^min] - 1[h≡2 mod 3^min] - 1[h+2≡0 mod 3^min]
```

再乘完整周期权重 `3^(R-max)`。来源 PR head `661f160b788bdfd8ab189ab4953b8592362f8db8` 已由 Lean CI #122、Factor-sum #110 验证，主分支提交 `b4a5dbb5b0dd4c1edc940b0a0acdee867620ce22`。

### C. 完整周期展开（PR #9）

`OmegaBalance/F3CorrelationPeriod.lean` 提供 `f3PeriodicTrunc`、与 `f3Trunc` 的精确兼容、周期指标乘积求和，以及 `f3PeriodicCorrelationSum_eq_layer_sum` / `f3PeriodicCorrelationSum_eq_explicit`。PR head `2669ff93ad750b81ce21d87e8f4997eb5c79fb04` 的 Lean CI #138 与 Factor-sum #126 成功，squash 合入主分支 `37da64866c5ae30c51ee9fc9c49e89eed92b125e`。

### D. 几何权重、capped depth 与权重桥（PR #10，已合入）

`OmegaBalance/F3CorrelationWeight.lean` 证明

```math
W_R(d)=\sum_{j,k=1}^{R}\mathbf 1_{\min(j,k)\le d}3^{R-\max(j,k)}
      =3^R-3^{R-\min(R,d)}-\min(R,d),
```

并给出递推 `f3CorrelationWeight_succ`。

`OmegaBalance/F3CorrelationDepth.lean` 定义 `f3CappedDepth`，明确保留 `v₃,R(0)=R`，证明 retained power 的整除/同余判据；交叉项统一用 `Nat.dist h 2` 处理 `h<2,h=2,h>2`；`f3PeriodicCorrelationSum_eq_weights` 将完整周期相关和写成

```text
2·W_R(depth_R(h)) - W_R(depth_R(dist h 2)) - W_R(depth_R(h+2)).
```

PR #10 最终 head `2395ad23dab91e0fadfe2e9ec71ff84faa5e906a` 的 Lean CI #166、Factor-sum #154 均成功；247 条声明公理审计、24 个 Lean 文件源码审计与一对一覆盖全部通过。随后 squash 合入主分支 `e8c9ec00d252ae1dce91e5c060d7bc0af1fb518d`。

## 当前工作：完整周期闭式（PR #11）

工作分支 `feat/f3-correlation-closed-period`，PR #11。新增 `OmegaBalance/F3CorrelationClosed.lean`：

- `f3CappedDepth_le`：capped depth 始终不超过 cutoff；
- `f3CappedDepth_two`、`f3CappedDepth_four`：两个后续边界值的 retained depth 为零；
- `f3PeriodicCorrelationSum_eq_closed`：把三个 `W_R` 全部代入，得到完整 `3^R` 周期相关和的精确闭式；
- `f3PeriodicCorrelationSum_zero_shift`：`h=0` 时精确为 `2·(3^R-1-R)`；
- `f3PeriodicCorrelationSum_two_shift`：`h=2` 时精确为 `-(3^R-1-R)`。

首次编译暴露 `v3_two` / `v3_four` 属示例模块、并不在核心 import 链中；没有为此把 Examples 引入核心，而改用已审计核心定理 `v3_eq_zero_of_not_dvd`。修正后的代码 head `5c656125f653d6be2bb0eaa4cd57a4e44dd2e0df` 已由 Lean CI #181 和 Factor-sum #169 成功验证：253 条声明仅依赖标准 Lean 公理，25 个 Lean 文件无 proof escape，审计覆盖 253/253，原有 144,240 项有限检查与 11 组边界测试也全部通过。

本次文档提交之后仍须以新的最终 PR head CI 为准，不能用上一个代码 head 的成功结果替代最终门禁。

## COR-1 下一阶段

有限完整周期闭式之后，剩余链条按以下顺序推进：

1. 将完整周期和除以 `3^R`，定义/连接三进绝对值核并证明固定 `h` 的归一化完整周期极限；零距离项必须保持 `|0|₃=0`。
2. 对固定 cutoff `R`，把完整周期平均推广到任意 Cesàro 长度，控制末尾不足一个周期的余项。
3. 证明 `F₃-F₃,R` 的 `L²` 尾部界（目标量级 `3^(1-R)`），再用 Cauchy–Schwarz 控制相关误差。
4. 完成 cutoff 极限与 Cesàro 极限交换，得到原始 `F₃` 的无限相关核
   `|h-2|₃+|h+2|₃-2|h|₃`。
5. COR-1 完成后推导 COR-2：固定 `r≥1` 的均方近似周期 `4/3^r`；`r=0` 单独由相关核处理。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

停止规则：INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，且精确版本构建、回归、公理、源码与覆盖门禁全部通过后，才结束全量任务；当前仍不满足停止条件。

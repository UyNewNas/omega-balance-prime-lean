# F₃ 全量形式化任务清单

此清单是周期推进的持久化状态。只有精确提交实际通过 Lean 内核、源码与公理审计的结果才登记为完成；纸面推导、有限计算或外部文献本身不替代 Lean 证明。

## 固定边界

- namespace：`OmegaBalance`。
- Lean 4.34.0；mathlib 固定提交 `5ed2965256430c3649e86755f9576b54eca72435`。
- 所有新增 theorem/lemma 均需进入 `scripts/Audit.lean`，且 `scripts/check_audit_coverage.py` 一对一覆盖。
- 禁止 `sorry` / `admit`、自定义数学公理、unsafe/native proof escape、同名假设伪装结论。
- PR #5 是独立的质因数求和研究线；F₃ 推进不覆盖其分支。
- 最终状态以精确 GitHub Actions head/相同文件树为准；运行中的 CI 不登记为通过。

## 总目标

| ID | 目标与前提 | 当前实现/依赖 | 状态 |
|---|---|---|---|
| INF-1 | 每个固定 `k≥1`，`F₃=±k` 的素数各有无穷多个 | `F3Infinitude.lean`；固定 mathlib 的 Dirichlet 定理 | **已完成并合入，PR #6** |
| INF-2 | 全体素数数列中连续两项的正→负、负→正转移各无穷次 | `F3SignChanges.lean`；显式 `ConsecutivePrimes` | **已完成并合入，PR #6** |
| COR-1 | 固定 `h≥0` 的完整整数相关核 | `F3Finite` + `F3CorrelationFinite/Layer/Period/Weight/Depth/Closed/Limit/Cesaro`；完整周期极限已合入，任意长度 quotient/remainder 层正在 PR #13 | **进行中** |
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

## COR-1 已完成并合入的有限层

### A. 完整周期幂三余数重叠

`OmegaBalance/F3CorrelationFinite.lean` 已证明单余数类计数、两个嵌套幂三余数类的精确交集 `modPairCount_eq`、平移计数 `modShiftPairCount_eq`，以及四种正/负层目标分别化为 `h≡0`、`h≡2`、`h+2≡0` 的兼容条件。

### B. 单层有符号相关核

`OmegaBalance/F3CorrelationLayer.lean` 的 `f3LayerCorrelation_eq` 将四个重叠数合并为

```text
2·1[h≡0 mod 3^min] - 1[h≡2 mod 3^min] - 1[h+2≡0 mod 3^min]
```

再乘完整周期权重 `3^(R-max)`。来源 PR head `661f160b788bdfd8ab189ab4953b8592362f8db8` 已由 Lean CI #122、Factor-sum #110 验证，主分支提交 `b4a5dbb5b0dd4c1edc940b0a0acdee867620ce22`。

### C. 完整周期展开

`OmegaBalance/F3CorrelationPeriod.lean` 提供 `f3PeriodicTrunc`、与 `f3Trunc` 的精确兼容、周期指标乘积求和，以及 `f3PeriodicCorrelationSum_eq_layer_sum` / `f3PeriodicCorrelationSum_eq_explicit`。PR #9 head `2669ff93ad750b81ce21d87e8f4997eb5c79fb04` 的 Lean CI #138 与 Factor-sum #126 成功，squash 合入主分支 `37da64866c5ae30c51ee9fc9c49e89eed92b125e`。

### D. 几何权重与 capped depth

`F3CorrelationWeight.lean` 证明

```math
W_R(d)=\sum_{j,k=1}^{R}\mathbf 1_{\min(j,k)\le d}3^{R-\max(j,k)}
      =3^R-3^{R-\min(R,d)}-\min(R,d).
```

`F3CorrelationDepth.lean` 保留 `v₃,R(0)=R` 的有限零约定，并用 `Nat.dist h 2` 同时处理 `h<2,h=2,h>2`。PR #10 head `2395ad23dab91e0fadfe2e9ec71ff84faa5e906a` 的 Lean CI #166、Factor-sum #154 成功，合入主分支 `e8c9ec00d252ae1dce91e5c060d7bc0af1fb518d`。

### E. 完整周期闭式

PR #11 已合入主分支 `69c4fff87efa056d1abb2cf0e6383262cf5eb2aa`。`F3CorrelationClosed.lean` 证明完整 `3^R` 周期相关和闭式

```text
3^(R-depth_R(dist h 2)) + 3^(R-depth_R(h+2)) - 2·3^(R-depth_R(h))
+ depth_R(dist h 2) + depth_R(h+2) - 2·depth_R(h),
```

以及 `h=0` 时 `2·(3^R-1-R)`、`h=2` 时 `-(3^R-1-R)` 两个特殊边界。来源 head `5699e4b8753f369d1098387575c816ce338983e0` 的 Lean CI #183、Factor-sum #171 均成功；253 条声明公理/覆盖审计和既有回归全部通过。

### F. 归一化完整周期极限

原 PR #12 已合入当前主分支提交 `32ff09bd5927a0f4a1a1f85019d554a31a86cf77`，新增 `OmegaBalance/F3CorrelationLimit.lean`。主要证明：

- `f3PadicKernel`：自然数上的实值三进核，`0` 处取 `0`，非零时为 `3^{-v₃(n)}`；
- `tendsto_f3NormalizedCappedKernel`：对所有输入（包括零）收敛到三进核；
- `tendsto_f3CappedDepthRatio_zero`：`depth_R(n)/3^R → 0`；
- `f3PeriodicCorrelationAverage_eq`：完整周期闭式除以 `3^R` 的精确分解；
- `tendsto_f3PeriodicCorrelationAverage`：固定 `h` 时
  `S_R(h)/3^R → kernel(dist h 2)+kernel(h+2)-2*kernel(h)`。

合并提交记录的验证来源为 head `f21ce187...`：Lean CI #204 与 Factor-sum #192 成功，260 条声明公理/覆盖审计、26 个 Lean 文件源码审计及既有回归全部通过。这里仅陈述已经合入的历史验证，不用它替代后续 PR 的精确 head 门禁。

## COR-1 当前推进：任意长度固定 cutoff 块（PR #13）

分支 `feat/f3-correlation-cesaro-blocks` 新增 `OmegaBalance/F3CorrelationCesaro.lean`，目标是完成“完整周期平均 → 任意初始长度”的有限余项层。目前已经写入并通过该分支代码 head 的 **library build** 的非空洞证明包括：

- `f3ModIndicator_periodic_pow_three`、`f3ResidueLayer_periodic_pow_three`、`f3PeriodicTrunc_periodic`：从每层模 `3^j` 指标逐层得到完整 `3^R` 周期；
- `f3PeriodicCorrelationTerm_periodic`：固定 cutoff 的相关 summand 本身同样 `3^R` 周期；
- `sum_range_periodic_mul_add_int`、`sum_range_periodic_div_mod_int`：对任意整数值周期函数证明精确的完整块 + 末尾余块分解；
- `f3PeriodicCorrelationPartialSum_eq_div_mod`：任意长度 `N` 的截断相关和精确分解为 `⌊N/3^R⌋` 个完整周期和长度 `N mod 3^R` 的终端块；
- `abs_f3ResidueLayer_le_one`、`abs_f3PeriodicTrunc_le`、`abs_f3PeriodicCorrelationTerm_le`：分别给出 `1`、`R`、`R²` 的统一界；
- `abs_f3PeriodicCorrelationPartialSum_le`、`abs_f3PeriodicCorrelationRemainder_le`：终端块绝对值最多 `3^R R²`，与总长度 `N` 无关。

前两次编译探针暴露并已修复：dependent `Decidable` 下直接 rewrite `Nat.ModEq`、非线性乘法交给 `omega`、以及 `(N / P : ℤ)` 被 Lean 解释为整数除法而非“自然数商再 cast”。最终陈述显式使用 `((N / P : ℕ) : ℤ)`，保住 Euclidean quotient/remainder 的数学含义。

代码 head `2b6872b634fe159763b39f2c8112668763e0dc7f` 的 Lean CI #215 已确认 library build 与三组 kernel regressions 成功；其覆盖检查因当时尚未加入本段 12 条新声明而失败，因此 **不能把 #215 记作最终门禁成功**。当前后续提交已补 `scripts/Audit.lean`，需以包含本文档的最终 PR head CI 为准后才可合入。

## COR-1 剩余链条

任意长度固定-cutoff 块层完成后，仍需按以下顺序推进：

1. 用 quotient/remainder 精确式和统一终端块界，收掉固定 `R` 的任意 Cesàro 长度极限，使其等于完整周期平均。
2. 证明 `F₃-F₃,R` 的 `L²` 尾部界（目标量级 `3^(1-R)`），再用 Cauchy–Schwarz 控制相关误差。
3. 完成 cutoff 极限与 Cesàro 极限交换，得到原始 `F₃` 的无限相关核
   `|h-2|₃+|h+2|₃-2|h|₃`；零点三进绝对值必须为 `0`。
4. COR-1 完成后推导 COR-2：固定 `r≥1` 的均方近似周期 `4/3^r`；`r=0` 单独由相关核处理。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

停止规则：INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，且精确版本构建、回归、公理、源码与覆盖门禁全部通过后，才结束全量任务；当前仍不满足停止条件。

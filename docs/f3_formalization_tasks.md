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
| COR-1 | 固定 `h≥0` 的完整整数相关核 | `F3Finite` + `F3CorrelationFinite/Layer/Period/Weight/Depth/Closed/Limit`；完整周期归一化极限正在 PR #12 核验 | **进行中** |
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

## 当前工作：归一化完整周期极限（PR #12）

工作分支 `feat/f3-correlation-period-limit`，PR #12。新增 `OmegaBalance/F3CorrelationLimit.lean`，目标只推进 cutoff 的完整周期极限，不提前声称任意长度 Cesàro 或原始 `F₃` 极限已经完成。

当前实现包括：

- `f3PadicKernel`：自然数上的实值三进核，明确 `f3PadicKernel 0 = 0`，非零时为 `3^{-v₃(n)}`；
- `f3NormalizedCappedKernel` 与 `tendsto_f3NormalizedCappedKernel`：证明有限 capped 几何项在固定参数上收敛到上述三进核；
- `f3CappedDepthRatio` 与 `tendsto_f3CappedDepthRatio_zero`：用 mathlib 的 `tendsto_pow_const_div_const_pow_of_one_lt` 证明 `depth_R(n)/3^R → 0`；
- `f3PeriodicCorrelationAverage_eq`：把完整周期闭式除以 `3^R`；
- `tendsto_f3PeriodicCorrelationAverage`：目标极限为
  `kernel(dist h 2) + kernel(h+2) - 2*kernel(h)`。

首次 CI head `07dc2c44c7a657d618d759d8ba1a342cd6a76982` 在 `F3CorrelationLimit.lean` 编译阶段失败，暴露的都是 Lean 接口/实现问题：四个使用 `ℝ` 除法的定义需 `noncomputable`；一个 `exact_mod_cast` 需要显式目标类型；最终 `Tendsto` 组合中的常数 `2` 需要显式 `const_mul`。这些错误没有改变数学陈述。

修正代码 head `c35e1ad97ffb1afee83f24655369850a30560ad7` 已确认 **library build 与 kernel regression tests 成功**；其后新增 7 条 `scripts/Audit.lean` 登记，当前最终分支 head 继续等待完整公理、源码、覆盖和有限回归门禁。只有最终 head 全绿后才把本阶段标为完成并合入。

## COR-1 剩余链条

归一化完整周期极限完成后，仍需按以下顺序推进：

1. 对固定 cutoff `R`，把完整周期平均推广到任意 Cesàro 长度，控制不足一个周期的末尾余项。
2. 证明 `F₃-F₃,R` 的 `L²` 尾部界（目标量级 `3^(1-R)`），再用 Cauchy–Schwarz 控制相关误差。
3. 完成 cutoff 极限与 Cesàro 极限交换，得到原始 `F₃` 的无限相关核
   `|h-2|₃+|h+2|₃-2|h|₃`；零点三进绝对值必须为 `0`。
4. COR-1 完成后推导 COR-2：固定 `r≥1` 的均方近似周期 `4/3^r`；`r=0` 单独由相关核处理。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

停止规则：INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，且精确版本构建、回归、公理、源码与覆盖门禁全部通过后，才结束全量任务；当前仍不满足停止条件。

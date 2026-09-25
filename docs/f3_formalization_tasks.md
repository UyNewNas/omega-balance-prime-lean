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
8. **任意长度 quotient/remainder 分解**：`F3CorrelationCesaro.lean`，PR #13 合入主分支 `f2a4f7595e5ee9d355d2d621438032121fc27dfe`。证明固定 `R` 时相关 summand 的周期性、任意部分和的完整块+终端块精确分解，以及终端块统一界 `≤3^R R²`。
9. **固定 cutoff 的任意长度 Cesàro 极限**：`F3CorrelationCesaroLimit.lean`，PR #14 经精确 head `3d27d52af8f1418036780514c9a6d9d66b2808a5` 的完整门禁通过后，合入主分支 `1dc54d0941d2ef1848b8bc794d82c6624b140398`。证明任意长度归一化截断相关平均收敛到完整 `3^R` 周期平均；不会把固定 cutoff 极限冒充原始 `F₃` 的无限相关核。

PR #14 的成功门禁确认 275 条 theorem/lemma 只依赖标准 Lean 公理，28 个 Lean 文件无 proof escape，声明审计覆盖一对一完整，既有 144,240 项有限检查和 11 组边界测试全部通过。

## COR-1 当前推进：`L²` 截断尾部

PR #15 分支 `feat/f3-correlation-tail-pointwise` 新增 `OmegaBalance/F3CorrelationTail.lean`，先把原始 `F₃` 与 `f3Trunc R` 的误差化成可计数的高赋值层。当前已写入并经中间 head `df49dd453f4aa66955d99a6f4e45df9d8fcc4479` 完整门禁验证的核心接口：

- `v3Excess R n = v3 n - R` 与 `f3Tail R n = f3 n - f3Trunc R n`；
- `f3Tail_of_mod_three_zero/two/one`：按 `n mod 3` 给出零、正 excess、负 excess 的精确点态公式；
- `f3Tail_sq_eq_neighbor_excess`：
  `(f3Tail R n)^2 = (v3Excess R (n+1))^2 + (v3Excess R (n-1))^2`，适用域 `n>1`；
- `sum_odd_eq_sq_int` / `v3Excess_sq_eq_odd_sum`：用前 `m` 个奇数和展开 excess 平方；
- `pow_three_dvd_iff_lt_v3Excess`：在 `n≠0` 时，`3^(R+t+1) ∣ n ↔ t < v3Excess R n`。

这一步只建立点态 `L²` 尾部的严格算术基础。尚未把它登记成 Cesàro 尾部界，也没有进行 cutoff/Cesàro 极限交换。PR #15 最终是否合入，以最终 head 再次通过完整门禁为准。

### COR-1：完整 tail 有限均方界

分支 `feat/f3-correlation-tail-bound-fix4` 的 exact head
`e3e117c0de02265475492f8de13291194947c8e5` 已通过 Lean #316 与
Factor-sum #304：library build、kernel regressions、axiom audit、source audit、
declaration coverage 与有限 F₃ 回归全部成功。新增并验证
`sum_Icc_v3Excess_sq_add_one`、`sum_Icc_v3Excess_sq_sub_one`、
`sum_Icc_f3Tail_sq_eq_neighbor_excess`、`sum_Icc_f3Tail_sq_le`。
下一层证明归一化的统一 Cesàro tail 界，只有 exact-head CI 再次通过后才登记完成。

### COR-1：cutoff majorant 衰减候选

分支 `feat/f3-correlation-tail-decay` 从归一化 tail 界候选 head
`e37f13baeac523e099cb9baeced98abb6823468c` 分出，新增
`tendsto_f3Tail_sq_cesaro_majorant`，目标为

```math
\lim_{R\to\infty}\frac{3}{3^R}=0.
```

该 theorem 只证明统一 majorant 随 cutoff 消失；不执行 cutoff/Cesàro 极限交换。
只有本分支 exact head 的完整 Lean/审计门禁通过后才登记为完成。

### COR-1：Cauchy–Schwarz 有限误差原语候选

分支 `feat/f3-correlation-tail-cauchy` 在 tail majorant 衰减候选之上新增 `sum_Icc_f3Tail_mul_sq_le`，把固定 mathlib 的 `Finset.sum_mul_sq_le_sq_mul_sq` 与完整 tail 有限均方界组合为有限相关误差原语：

```math
(\sum_{2\le n\le N} E_R(n)g(n))^2
\le\left(\frac{N+1}{3^R}+\frac N{3^R}\right)\sum_{2\le n\le N}g(n)^2.
```

其中 `E_R(n)=F_3(n)-F_{3,R}(n)`。只有 exact-head CI 全绿后才登记完成。

### COR-1：平移 tail 与原始二阶矩候选

分支 `feat/f3-correlation-tail-shift` 继续补相关误差所需的平移控制：
`sum_Icc_f3Tail_sq_add_shift`、`sum_Icc_f3Tail_sq_shift_le`、
`f3Tail_zero`、`sum_Icc_f3_sq_shift_le`。这使固定移位 `h` 的 tail 二阶矩
和原始 `F₃(n+h)` 二阶矩都可直接喂给 Cauchy–Schwarz。只有 exact-head CI
全绿后才登记为完成。

### COR-1：相关误差分解候选

`feat/f3-correlation-tail-error` 新增 `f3_correlation_sub_trunc_eq_tails` 和 `sum_Icc_f3Tail_shift_mul_sq_le`，分别记录原始/截断相关误差的精确 tail 分解与平移 tail 的有限 Cauchy–Schwarz 控制。exact-head CI 全绿前保持候选状态。

### COR-1：有限相关误差求和恒等式候选

分支 `feat/f3-correlation-tail-error-sum` 新增求和版 raw/truncated 相关误差恒等式；只有 exact-head CI 全绿后才登记完成。

### COR-1：三个相关误差交叉项平方界候选

`feat/f3-correlation-tail-error-bound` 新增三个专用 Cauchy–Schwarz 界，分别控制 `tail·raw_shift`、`raw·tail_shift` 与 `tail·tail_shift` 的有限求和平方；它们只使用已登记的 tail/raw 二阶矩界。exact-head CI 全绿前保持候选状态。

## COR-1 剩余链条

1. 把 `v3Excess_sq_eq_odd_sum` 与幂三整除密度计数结合，证明 `F₃-F₃,R` 的 `L²` Cesàro 尾部界。目标至少达到既定 `O(3^(1-R))`；纸面计算提示可进一步得到精确极限 `2/3^R`，只有完成 Lean 证明后才登记为定理。
2. 用 Cauchy–Schwarz 控制原始相关平均与固定 cutoff 相关平均之间的误差。
3. 完成 cutoff 极限与 Cesàro 极限交换，得到原始 `F₃` 的无限相关核 `|h-2|₃+|h+2|₃-2|h|₃`。
4. 从 COR-1 推导 COR-2：固定 `r≥1` 的均方近似周期 `4/3^r`；`r=0` 必须单独处理，不能套该简式。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。

## 停止规则

只有 INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，上游依赖经过信任审计，且精确版本的构建、回归、公理、源码、覆盖全部通过后，才结束全量任务。当前尚未满足停止条件。

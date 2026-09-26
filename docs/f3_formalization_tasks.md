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
| COR-1 | 固定 `h≥0` 的完整整数相关核 | **证明完成；PR #19 exact-head 已全绿，待 stacked 分支最终主线集成** |
| COR-2 | 固定 `r≥1` 的均方近似周期 `4/3^r` | **证明完成；PR #20 exact-head 已全绿，待 stacked 分支最终主线集成** |
| DEN-1 | 素数单点比例 `3^(-k)`、层级尾部 `3^(1-K)` | **证明完成；consumer exact head `0946893…` 已全绿，待 stacked 主线集成** |
| DEN-2 | 固定乘子升层密度；含乘数 17 的 `1/2,1/3,1/9,…` 条件分布 | **进行中：`1/2` 已完成；高输出层输入桥 exact head `aa193c3…` 已全绿；`j≥1` 的 `3^{-j}` 仍待完成** |
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

### COR-1：完整有限相关误差平方界候选

`feat/f3-correlation-tail-error-combined` 新增 `F3CorrelationTailError.lean`，定义有限 tail/raw 二阶矩上界并证明 `sum_Icc_f3_correlation_error_sq_le`：原始相关与截断相关的有限求和差平方，由三个已分解交叉项的 Cauchy–Schwarz 上界统一控制。该层仍不执行 Cesàro/cutoff 极限交换；exact-head CI 全绿前保持候选状态。

PR #17 head `8e52a2f558b0b251e5c180ffa877add19fbed837` 的 Lean #348 精确失败于三个实值辅助定义的可计算性：`f3TailMassUpper`、`f3TailShiftMassUpper`、`f3CorrelationErrorSqUpper` 使用实数除法而需 `noncomputable`。修复提交 `0b9745132492fc902bc0041bebaf5c4804454c6f` 仅把这三个定义改为 `noncomputable def`，不改变 theorem 陈述或证明项；当前位于 `feat/f3-correlation-tail-noncomputable-fix`，等待 exact-head PR CI 验证后才登记完成。

### COR-1：归一化有限相关误差平方界候选

分支 `feat/f3-correlation-tail-cesaro-error-sq` 在上述可计算性修复之上新增 `f3_correlation_cesaro_error_sq_le`。对 `N>0`，它把完整 raw/truncated 相关误差平方界严格除以 `N²`，作为后续构造与 `N` 无关且随 `R→∞` 消失的统一 majorant 的接口。本层不声称极限交换；exact-head CI 全绿前保持候选状态。


### COR-1：与平均长度无关的相关误差 majorant

exact head `e4c9f8f61645ff90186ec9db0b935ccc9fa11810` 已通过 Lean #358
与 Factor-sum #346。定义
`f3CorrelationErrorSqMajorant R h = 9(2h+3)(2/3^R+1/3^(2R))`，并验证
`f3CorrelationErrorSqUpper_div_sq_le_majorant` 与
`f3_correlation_cesaro_error_sq_le_majorant`。二者只使用 `N>0`
导出的 `2N+1≤3N` 与 `2N+2h+1≤(2h+3)N`，给出与平均长度 `N`
无关的 raw/truncated 相关平方误差界。该 exact head 的 axiom audit 为
314 declarations、source audit 为 31 Lean files 无 proof escape、Audit
coverage 314/314、有限回归 144240 PASS。

### COR-1：统一相关误差 majorant 的 cutoff 衰减候选

后续候选 `tendsto_f3CorrelationErrorSqMajorant` 对每个固定 `h` 证明

```math
9(2h+3)\left(\frac{2}{3^R}+\frac1{3^{2R}}\right)\to0.
```

它只关闭 uniform majorant 的 cutoff 衰减，不把此结论本身冒充
raw correlation 的双极限交换；exact-head CI 完整通过后才登记完成。

候选 head `24f1a0207149a28c59873890464dd19088d0ec5d` 的 Factor-sum #349 成功，但 Lean #361 在 `F3CorrelationTailError.lean` build 阶段失败：新增极限定理使用 `𝓝` 邻域记号，而本模块未打开 `Topology`。后续修复只加入 `open Filter Topology`，不改变定理陈述与证明结构；修复 head 仍需重新通过完整门禁。

修复 head `68539658e1a136102da5620fb7cd7fa05b1b3414` 的 Factor-sum #350 成功；Lean #362 进一步通过到该极限定理最后的 `simpa`，仅剩 `/` 与乘逆元表示未归一化的 type mismatch。后续修复在最终 simplifier 中加入 `div_eq_mul_inv`，不改变数学陈述。

最终修复 head `5c47684ca9fd579da817ddbf35e74ae34dd53f06` 已通过 Lean #363 与 Factor-sum #351：library build、kernel regressions、axiom/source audit、declaration coverage 与有限 F₃ 回归全部成功。Axiom audit 为 315 declarations，source audit 为 31 Lean files 无 proof escape，Audit coverage 315/315，有限回归 144240 PASS。因此 `tendsto_f3CorrelationErrorSqMajorant` 正式登记完成；它只证明固定 `h` 的 uniform square-error majorant 随 cutoff 消失，尚不单独构成 raw correlation 的双极限交换。

### COR-1：自然 Icc 截断相关 Cesàro 桥接

分支 `feat/f3-correlation-trunc-icc-cesaro-v1` 已把自然窗口 `2≤n≤N`
上的截断相关平均与从 0 开始的周期模型严格桥接。修复 head
`26ee1d6902fdb6927e1a1d06caa269c434b9e5ab` 已通过 Lean #368 与
Factor-sum #356：library build、kernel regressions、axiom/source audit、
declaration coverage 与有限 F₃ 回归全部成功。Axiom audit 为 320 declarations，
source audit 为 32 Lean files 无 proof escape，Audit coverage 320/320，有限回归
144240 PASS。核心接口为 `f3TruncCorrelationIccSum_eq_periodic_sub_boundary`、
`f3TruncCorrelationIccAverage_eq` 与 `tendsto_f3TruncCorrelationIccAverage`。
本分支将它与已验证的 uniform majorant cutoff 衰减合流，为最终 raw/cutoff
双极限交换准备同一文件树；尚不宣告双极限已经完成。


### COR-1：原始 F₃ 相关核完成（stacked exact-head）

PR #19 的 exact head `7398ad8edbe4f9d569d926d1c226529bc14755cd`
已通过 Lean #378 与 Factor-sum #366。新增 `F3CorrelationLimitExchange.lean`，
核心定理 `tendsto_f3CorrelationIccAverage` 对每个固定 `h` 证明自然窗口
`2≤n≤N` 上的 raw F₃ 相关 Cesàro 平均收敛到

```math
|h-2|_3+|h+2|_3-2|h|_3,
```

其中源码以
`f3PadicKernel (Nat.dist h 2) + f3PadicKernel (h+2) - 2*f3PadicKernel h`
表达，且 `f3PadicKernel 0 = 0`。证明显式先选 cutoff，再选固定 cutoff 下的
Cesàro 长度；没有把点态截断相等冒充极限交换，也没有切换到素数子序列。
Lean #378 的完整日志确认：Axiom audit 324 declarations、Source audit 33 Lean
files 无 proof escape、Audit coverage 324/324、有限回归 144240 PASS，全部边界
回归通过。验证后 PR #17 head 分支已非强制 fast-forward 到同一 exact SHA。

### COR-2：幂三移位的相关核代数层候选

分支 `feat/f3-correlation-mean-square-period-v1` 从上述 exact verified COR-1
head 分出，新建 `F3CorrelationApproxPeriod.lean`。当前候选先完成 `r>0`
时的核值化简：

- `f3PadicKernel_pow_three`；
- `f3PadicKernel_pow_three_add_two`；
- `f3PadicKernel_dist_pow_three_two`；
- `f3CorrelationKernel_pow_three`；
- `f3CorrelationKernel_meanSquare_pow_three`，目标值为
  `4 / (3:ℝ)^r`。

这一步只关闭 COR-2 的核代数，不把它冒充均方 Cesàro 极限；仍需证明
`(F₃(n+3^r)-F₃(n))²` 平均与 `2R(0)-2R(3^r)` 的极限连接。新声明已加入
`scripts/Audit.lean`，只有 exact-head CI 全绿后才登记为完成。


## COR-1 / COR-2 剩余链条

1. COR-1 的证明层已经 exact-head 全绿；剩余只是按 stacked PR 顺序最终集成主分支。
2. COR-2：分支 `feat/f3-correlation-shift-square-v1` 候选新增固定移位平方平均边界公式与 `tendsto_f3ShiftSquareIccAverage`，并把均方差有限和精确展开为两个平方平均与一个交叉相关平均。
3. 候选 `tendsto_f3MeanSquareShiftIccAverage_pow_three` 对 `r>0` 代入 COR-1 与幂三核化简，目标正是 `4/3^r`。该分支仅在 exact-head CI 全绿后登记完成；`r=0` 仍单独由 COR-1 的 `h=1` 相关核处理，不能套该简式。

### COR-2：CI 修复记录

PR #20 的 COR-2 主定理在提交 `34e0946d10d6476a6ebe4235e91376ec3a192b18` 获得 exact-head 完整门禁：Lean #408、Factor-sum #396 均成功；公理审计 340 条声明仅使用标准 Lean 公理，35 个 Lean 文件无 proof escape，Audit 340/340 一对一覆盖，144,240 项有限检查全部 PASS。因此 `tendsto_f3MeanSquareShiftIccAverage_pow_three` 对 `r>0` 已登记完成。本轮继续补 `r=0` 边界：单独计算 shift-one 相关核为 `-2/3`，并候选证明 shift-one 均方极限为 `16/3`；它不使用也不修改 `4/3^r` 的 `r>0` 定理。

### COR-2：shift-one 边界 exact-head

PR #20 exact head `7824f25eb31506eac747590ddfe99defc9913a4f` 已通过 Lean #410 与 Factor-sum #398。Lean #410 日志确认：Axiom audit 344 declarations，仅标准 Lean 公理；Source audit 35 Lean files、无 proof escape；Audit coverage 344/344 恰好一次；有限回归 144240 PASS。该 head 单独证明 shift-one 相关核 `-2/3` 与均方极限 `16/3`，没有把 `r=0` 错套进 `4/3^r`。

### DEN-1：AP 渐近来源与版本边界

已核验 ANT：`PrimeNumberTheoremAnd/Wiener.lean` 的 `WeakPNT_AP` 给出 von Mangoldt 加权 AP 渐近，`PrimeNumberTheoremAnd/Consequences.lean` 的 `chebyshev_asymptotic_pnt` 给出固定原始剩余类中的素数 `log p` 加权渐近。ANT 当前 pin 为 Lean `v4.33.0-rc1` / mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`，本仓库固定 Lean `v4.34.0` / mathlib `5ed2965256430c3649e86755f9576b54eca72435`，因此不直接整仓依赖或升级；后续只适配所需 AP 计数接口并在本仓库 pin 上重编译审计。

分支 `feat/f3-prime-density-residues-v1` 的 exact head `f78657256300009b3c51d271ae607cd58cf1ae86` 已通过 Lean #417 与 Factor-sum #405。新增 `v3_eq_iff_pow_three_dvd_not_succ`、`f3_prime_eq_pos_level_iff`、`f3_prime_eq_neg_level_iff`，把精确 `±k` 层化为嵌套 `3^k` 与 `3^(k+1)` 整除层之差。Lean #417 日志确认：Axiom audit 347 declarations，仅标准 Lean 公理；Source audit 36 Lean files、无 proof escape；Audit coverage 347/347 恰好一次；有限回归 144240 PASS。该算术前端正式登记完成，但 DEN-1 的渐近密度定理仍未完成。\n\n外部优先检索还找到 `plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e` 的 `src/latest/ErdosProblems/Erdos730/PNTAP.lean`：其 `primeAPCountingReal_normalized_tendsto` 已从同源 `chebyshev_asymptotic_pnt` 推出未加权 AP 素数计数 `primeAPCountingReal A a x / (x / log x) → (φ(A))⁻¹`。该快照使用 Lean 4.33.0 / mathlib 4.33.0（manifest mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`），仍与本仓库 4.34.0 pin 不同；因此下一步优先做该现成证明的最小兼容适配，而不是重新发明 partial summation，也不把它未经重编译直接当作本仓库定理。

DEN、LOG、RUN 不由有限周期计算替代，保持未完成状态。


### DEN-1：负层真实素数精确密度已通过 exact-head

consumer exact head `52600809f57835ee7e5182f09c3c72ea2eac0893` 已通过
Lean #526 与 Factor-sum #514。该 head 将 `F₃=-k` 的真实素数集合严格识别为
`p ≡ 1 (mod 3^k)` 与 `p ≡ 1 (mod 3^(k+1))` 的有限集差，并证明

```math
\frac{\#\{p\le x: p\text{ prime},\ p>3,\ F_3(p)=-k\}}{x/\log x}
\longrightarrow 3^{-k},\qquad k\ge1.
```

对应接口为 `f3PrimeNegLevelCountingReal_eq_APDifference` 与
`f3PrimeNegLevelCountingReal_normalized_tendsto`。Lean #526 的 build、
kernel regression、axiom/source audit、declaration coverage 与有限 F₃
检查全部成功；axiom log 覆盖 369 个登记声明，有限检查 144240 PASS。

### DEN-1：正层真实素数精确密度候选

在上述 exact verified head 上新增 `F3PrimeDensityExactPos.lean`。候选层先证明
`p % 3^k = 3^k-1 ↔ 3^k ∣ p+1`，并把 exact `F₃=+k`（包含 `p=2,k=1`
这个真实有限边界）识别为 `-1 mod 3^k` 类去掉 `-1 mod 3^(k+1)` 类。
随后复用同一个未加权 AP-PNT 桥和 Euler-totient 差，目标定理
`f3PrimePosLevelCountingReal_normalized_tendsto` 的常数同样为 `3^{-k}`。
新声明已加入 `scripts/Audit.lean`；只有该新 exact head 完整门禁通过后才登记完成。

### DEN-2：乘数 17 的第一条件分支计数

exact head `ffe62a3331f38f9b0312e4c16da723e2f60d9e61` 已通过 Lean
#36233546297 与 Factor-sum #36233546285。该层新增真实事件集合
`f3PrimeMul17EqTwoPrimes`，并验证

```math
\{q\le x:q\text{ prime},F_3(q)=-2,F_3(17q)=2\}
=
\{q\le x:q\text{ prime},q\equiv10\pmod{27}\},
```

从而由未加权 AP-PNT 得到分子标准归一化密度
`1/φ(27)=1/18`。`f3PrimeMul17EqTwoRelativeRatio_tendsto` 进一步对真实计数商证明相对极限
`1/2`。exact head `142ae6013cda00a01ba1bc018d2ae8f2a3e54a98` 已通过 Lean
#36233902351 与 Factor-sum #36233902369；Lean 日志确认 Axiom audit 394
条声明、Source audit 49 Lean files 无 proof escape、Audit coverage 394/394，
有限检查 144240 PASS。因此乘数 17 的首分支 `1/2` 正式登记完成。后续仍需一般
`F₃(17q)=2+j`（`j≥1`）的 `3^{-j}` 条件分布。

## 停止规则

只有 INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，上游依赖经过信任审计，且精确版本的构建、回归、公理、源码、覆盖全部通过后，才结束全量任务。当前尚未满足停止条件。

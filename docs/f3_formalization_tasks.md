# F₃ 全量形式化任务清单

## 2026-09-30 07:16 UTC：无条件 RUN 精确验证及最新主线组合

无条件代码 `69c48f9e74426ef8004a761752c59d524f2d7fdb` 的
[push 36679099690](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679099690) 与
[PR 36679105586](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679105586)
全部成功。实际日志中 `MaynardBFT.consecutive_primes`、
`OmegaBalance.bftbPrimeIndexRuns_unconditional`、
`OmegaBalance.f3PrimeIndexRunStarts_infinite_unconditional` 均仅依赖
`propext`、`Classical.choice`、`Quot.sound`。完整产生器、项目构建、内核回归、
650 个依赖模块源码/固定版本检查、99 个项目文件、646+1 精确审计和144240有限检查通过。

最终接口是：每个 L≥1 存在仅依赖 L 的自然数 C，对每个非零整数 c，
全体素数枚举 `Nat.nth Nat.Prime` 中有无限多个起始下标 r，使连续 L 个素数
的 F₃ 全为 c，且末首素数之差≤`f3RunModulus c * C`。长度1保留零跨度情形。
`F3PrimeIndexRunAt` 明确使用全体素数，不是某个筛选子列；原条件接口由实际
上游定理产生，不再作为未经证明的前提。

新增五条声明：`bftbPrimeIndexRuns_unconditional`、
`f3PrimeIndexRunStarts_infinite_unconditional`（F3BFTBMaynardAdapter），以及
`bftb_eventually_log_rpow_le_rpow`、`bftb_eventually_rpow_le_half_rpow_div_rpow_log`、
`bftb_eventually_floor_rpow_le_floor_half_rpow_div_rpow_log`（F3BFTBCutoff）。
原始固定 Lean/mathlib、真实参数边界和全部审计门禁保持不变。第三方来源说明
继续如实标注作者代码许可范围尚未确认；不把署名或沉默解释为许可。

随后真实三方合入已验 Haar 主线 `f45cd8a7586609555e8f307d25c38fee5c105249`，
保留双方全部数学源码字节及文档。组合候选是684条项目声明+1必需上游产生器、
105个项目文件；本地15项兼容测试、6项审计规则测试与源码/覆盖检查通过。
这个新增组合树仍须自己的完整 CI，不能用69c48f9的旧run替代。

原五项目标中的 INF/COR/DEN/LOG 已在主线；RUN 已有无条件内核证明，等待最新
组合验证与合并。全部接收 proof 任务尚未完成：全局 PAT、REC 等剩余概率/等待律、
其它登记节点继续开放。单次 Haar 范围已合入 PR51，不扩张为完整 REC 完成。


此文件是持续推进的权威任务账本。只有精确提交实际通过 Lean 构建、回归、公理、源码与声明覆盖门禁的结果才标记为完成；纸面推导、Python 有限验算或外部文献本身不算 Lean 证明。

## 最新组合验证（2026-09-30，优先于历史状态行）

代码head `febe6175d83d8f2fa92b6f8a3d2b610016119a22` 完整601条门禁通过（PR run36660504382、push run36660499386）。COR-1/2与LOG-1已经非条件证明；DEN实际层计数的x/log x归一化渐近及17倍条件比例已证明，显式相对全部素数计数的3个比例接口仍待补。无条件RUN-1/2仍受产生器兼容阻塞；原有条件RUN接口不冒称完成。PAT-L1–3已合入，所有已接收新proof的未完成局部/全局节点保留在接收账本，不因前三项目进展而关闭总任务。

合并差异专项复核：旧栈66b8e838的91个OmegaBalance源码blob逐一保持；根import为两侧并集88项，Audit为两侧并集601项，无重复/遗漏，最新master文件零丢失。实际manifest与历史成功artifact字节一致；新组合已真实编译和公理复验。当前文档提交仍独立检查后方可合并。

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
| DEN-2 | 固定乘子升层密度；含乘数 17 的 `1/2,1/3,1/9,…` 条件分布 | **证明完成；一般 `j≥1` 的 `3^{-j}` 已在 exact head `8029c306…` 全绿，待 stacked 主线集成** |
| LOG-1 | 真正 `log₃-ad U` 的收敛、同态、等距及 F₃ 连接 | **进行中；收敛、主导项、等距/赋值连接及 formal coefficient bridge 已 exact-head 验证，乘法同态仍未完成** |
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

### DEN-2：乘数 17 高层条件分布（exact-head 已验证）

分支 `feat/f3-prime-density-mul17-high-count-v1` 从 exact-green 的 PR #22 head `faa696ed655e18a20bc3eb80d4905d72cb640f32` 分出。新增候选层把 `F₃(17q)=k`（`k≥3`）精确识别为唯一 primitive residue `f3Mul17Residue k mod 3^k` 去掉其模 `3^(k+1)` 的唯一 lift，并复用未加权 AP-PNT 与已验证的 `F₃(q)=-2` 输入密度，目标为每个 `j≥1` 的真实条件计数比例趋于 `3^(-j)`。exact head `8029c30612830f20ee4ce77e5afbf045bc2af30f` 已通过 Lean #577 与 Factor-sum #565；Axiom audit 409 declarations、Source audit 51 Lean files、Audit coverage 409/409、有限检查 144240 PASS。因此一般 `j≥1` 的 `3^(-j)` 条件分布证明层正式登记完成，仍待 stacked 主线集成。


### LOG-1 convergence layer: exact-head verified

Commit e48150f668cc5d8321877fa1a541f59077166057 adds
OmegaBalance/F3PadicLog.lean. It defines the genuine Q_3 logarithm series,
proves the natural-denominator inverse norm bound, a geometric norm majorant,
term decay, absolute summability on the open unit ball, and the resulting
HasSum for every admissible F3 input n > 1 with 3 not dividing n. All seven
new theorem declarations are registered in scripts/Audit.lean.

Exact-head gates: Lean run 607 (36241672820) SUCCESS and Factor-sum run 595
(36241672808) SUCCESS. Build, kernel regressions, axiom audit,
source/declaration coverage, and finite regressions all passed at the same
commit. This closes only the convergence/existence sublayer of LOG-1;
multiplicativity and valuation/isometry remain open.


### LOG-1 radius-one-third domain bound (candidate)

Branch `feat/f3-padic-log-dominant-term-v1` adds
`f3PadicDelta_norm_le_one_third`. For every admissible input
`n > 1` with `3 ∤ n`, it sharpens the open-unit-ball fact to
`‖U(n)-1‖₃ ≤ 1/3`.

The proof uses the already verified exact depth formula
`‖f3PadicDelta n‖ = 3^{-natAbs(F₃(n))}` together with nonvanishing of
`F₃(n)` on this domain. This is the discrete-radius input needed for a
strict higher-log-term bound and the later logarithmic isometry. It does not
claim multiplicativity or valuation preservation yet; only exact-head CI can
promote this candidate to verified status.


### LOG-1 dominant higher terms (candidate)

On top of the verified radius-one-third bound, the same branch now adds
`f3PadicLogTerm_valuation`, an exact valuation formula for every nonzero
logarithm-series term, and specializes it to the F₃ coordinate.  Using
`3 * padicValNat 3 (k+1) ≤ k+1`, the candidate theorem
`f3PadicLogTerm_delta_valuation_gt` proves that each term with `k>0`
has valuation strictly larger than the linear displacement.  Equivalently,
`norm_f3PadicLogTerm_delta_lt_first` gives strict norm domination by the
first term.  This is the key local input for proving
`‖log(U(n))‖₃ = ‖U(n)-1‖₃`; the infinite-tail/isometry theorem itself is
not claimed until a separate exact-head proof closes the limit step.



### LOG-1 dominant-term layer: exact-head verified

Exact head `218e173ce812135a06b8fe2f1707a9c5931ee36d` passed Lean #623
(run `36243542287`) and Factor-sum #611 (run `36243542271`) completely.
Therefore `f3PadicDelta_norm_le_one_third`, `f3PadicLogTerm_valuation`,
`f3PadicLogTerm_delta_valuation_gt`, and
`norm_f3PadicLogTerm_delta_lt_first` are now promoted from candidate to
verified. This proves every genuinely higher logarithm term has strictly
larger 3-adic valuation than the linear displacement.

### LOG-1 logarithmic isometry layer: exact-head verified

Branch `feat/f3-padic-log-isometry-v2` adds
`OmegaBalance/F3PadicLogIsometry.lean`. It defines the nonlinear tail,
bounds the whole tail by the next discrete 3-adic radius, splits the genuine
logarithm into its linear term plus tail, and targets the exact identities

```math
||log(U(n))||_3 = ||U(n)-1||_3,
v_3(log(U(n))) = |F_3(n)|,
F_3(n) = -chi(n) v_3(log(U(n))).
```

All eight new theorem declarations are registered in `scripts/Audit.lean`.
Exact head `b09e06d67329c309290c3252e81249fd518fb0d8` passed Lean #626
(run `36244366034`) and Factor-sum #614 (run `36244366033`). The Lean log
confirms Axiom audit 437 declarations with only standard Lean axioms, Source
audit 55 Lean files with no proof escapes, Audit coverage 437/437 exactly once,
and 144240 finite checks PASS. Therefore the genuine logarithmic norm
isometry, nonvanishing, exact valuation preservation, and signed bridge
`F₃(n) = -χ(n) v₃(L(n))` are formally verified. Multiplicativity
`L(mn)=L(m)+L(n)` remains a separate LOG-1 task.


### LOG-1 formal coefficient bridge repair

Integrated head `9d05202fdc3f8ae4862bfe0a906c5bb9fae32abd` exposed a real pinned-version
obstruction: Lean run 636 (36247112572) failed because
`PowerSeries.eval₂` requires `IsLinearTopology ℚ_[3] ℚ_[3]`, which is not
available for the usual topology on `ℚ_[3]`.  The failed analytic-evaluator
interfaces are therefore removed rather than papered over with a discrete
topology.

The repair branch records the topology-free bridge actually justified by the
pinned APIs: each project log term is the matching coefficient of
`PowerSeries.log`, the convergent project log is the HasSum of those
nonconstant coefficients, and `NormedSpace.exp` is the HasSum of the formal
`PowerSeries.exp` coefficients.  It also records the two pinned formal
exp/log substitution identities.  This repair remains candidate until its
exact head passes build, axiom/source, declaration-coverage and regression
gates.  Multiplicativity `L(mn)=L(m)+L(n)` remains the next LOG-1 target.


### LOG-1 formal coefficient bridge：exact-head verified

修复 head `77d25f892e8204a2b363036006b3d3efdbee798c` 已通过 Lean run
`36248316381` 与 Factor-sum run `36248316358`。因此
`f3PadicLogTerm_eq_powerSeries_coeff`、
`hasSum_f3PadicLog_powerSeries_coeff`、
`f3PadicExp_eq_tsum_powerSeries_coeff` 以及固定 mathlib 的两条 formal
exp/log substitution identity 正式登记为 verified。这里没有伪造
`IsLinearTopology ℚ_[3] ℚ_[3]`，也没有把 totalized `NormedSpace.exp`
冒充全局收敛的 p-adic exponential。

### LOG-1 multiplication domain reduction（candidate）

分支 `feat/f3-padic-log-mul-domain-v1` 在上述 exact-green head 上新增
`F3PadicLogMulDomain.lean`。它候选证明 admissible 输入乘积的精确
principal-unit displacement

```math
\Delta(mn)=\Delta(m)+\Delta(n)+\Delta(m)\Delta(n),
```

同时证明该 nonlinear displacement 仍位于 log 的开单位球、其实际 log
级数以 `f3PadicLog (m*n)` 为和，并把最终乘法同态严格归约到真正的分析恒等式

```math
\log(1+x+y+xy)=\log(1+x)+\log(1+y).
```

本层不把这个 reduction 冒充乘法同态；只有 exact-head CI 全绿后才登记完成。

## 停止规则

只有 INF、COR、DEN、LOG、RUN 全部目标得到非空洞 Lean 证明并集成主分支，上游依赖经过信任审计，且精确版本的构建、回归、公理、源码、覆盖全部通过后，才结束全量任务。当前尚未满足停止条件。

## 2026-09-27 状态覆盖（Round 24）

以下状态以 stacked exact head `0d5e9c3a9433eb43d0b773bf16da363ef528a0c8` 的完整成功门禁为准，
覆盖本文件上方尚未及时改写的旧状态行。Lean run `36299729802` 与 Factor-sum
run `36299729796` 均成功；565 declarations 仅标准 Lean axioms，86 Lean files
无 proof escape，Audit 565/565 exactly once，有限回归 144240 PASS。

| ID | 当前权威状态 |
|---|---|
| INF-1 / INF-2 | **完成** |
| COR-1 / COR-2 | **证明层完成，stacked exact-green；待主线最终集成** |
| DEN-1 / DEN-2 | **证明层完成，stacked exact-green；待主线最终集成** |
| LOG-1 | **证明层完成，含 genuine p-adic log、signed valuation bridge 与 `f3PadicLog_mul`；stacked exact-green** |
| RUN finite CRT / maximal / exact-pattern / ordered block | **完成，stacked exact-green** |
| RUN residue-class packaging | **本轮完成，stacked exact-green** |
| RUN many-primes + uniform outside composite → arbitrarily-far bounded residue runs | **本轮完成，stacked exact-green** |
| RUN unconditional many-primes producer | **未完成；当前唯一主要数学依赖是可信 BV/Maynard--Tao producer 及接口兼容** |
| RUN final unconditional constant-F₃ consecutive runs | **未完成** |
| stacked → master | **未完成；master 仍未集成本轮 stacked 链** |

本轮新增 exact-green 接口与精确上游阻塞记录见
`docs/f3_progress_round_24.md`。不得把当前 conditional many-primes 入口
解释成 BFTB/Shiu 已经无条件形式化完成。

## 2026-09-30：独立接收 F3-PAT-1 局部证明

来源 `4c532a866ad60bbe0492a928b41fe1fa1c1766e6`，接收基线 master `b4c14823d9a97a45770ed42379673d39b5295be6`。全分支接收扫描正在独立完成；本条不宣称已扫描完全部来源。

- PAT-L1：`v3_eq_of_modEq_pow_of_lt`，A、B均非零，A≡B mod3^R 且v3(B)<R ⇒v3(A)=v3(B)。
- PAT-L2：四点模729代表与三个乘积加一代表，两条精确模类定理。
- PAT-L3：`f3_pat1_pattern_of_mod729`，n>1、d>0及n≡5,d≡1 mod729 ⇒七个指定有符号值；不要求素性。
- 实现：`OmegaBalance/F3FourPrimePattern.lean`，4条定理均进入审计，3个定义区分七值模式和素数配置。
- 局部已验证代码提交 `5f94116a7bddd73b37ebf4634a8d71f16ff54fe9`，[Lean CI](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36658263293) 全门禁成功。
- [形式化映射](proofs/f3/four_prime_construction/formalization.md) / [外部查重记录](f3_external_reuse.md)。
- 剩余：PAT-L4复杂度、PAT-L5局部因子与奇异乘积、EXT-GT2、PAT-L6渐近、PAT-L7无穷性；这些未完成项不妨碍局部已验证结果但禁止把全局PAT标LEAN-PROVED。五大原始目标继续保留。

## 2026-09-30：当前 master 三方集成候选

基线 `ad603cf4013db10365aa96e4f5a4de4d8fdac243` 已含独立验证合入的 PAT 局部结果与 ROOT-4 纸面修正。集成来源为 PR #28 exact `66b8e8380d240868c5fdd784eeb6aedb966cae3a`，不以旧 PR body 声称的 base 替代实际提交图。

当前候选复用 COR-1/2、DEN-1/2、LOG-1 完整声明，保留全部正性/非零/固定参数边界，并保留已验证 RUN 有限/条件接口。源版本已绿；本组合树仍须精确 CI，当前不登记主线完成。`r=0` 的平移1均方极限为16/3，非4；17倍比例条件是原素数 q 满足F3(q)=-2；log域是n>1且3∤n。RUN最终无条件目标继续阻塞于兼容且可信的产生器。

完整来源接收、水位、稳定/临时结果ID、量词和缺失依赖见 [接收账本](f3_proof_intake.md) 及 [机器可读记录](f3_proof_intake.json)。扫描完成不代表形式化完成；广义F3D关联审读另行记录，未读内容不升水位。

## 2026-09-30：下一局部代码候选（CI待验证）

- DEN显式全素数分母：`F3PrimeRelativeDensity.lean`，7条定理，模1AP计数等于真实全素数计数、PNT极限1、最终非零、薄商极限桥与±k/尾部实际比例。沿用已证计数，未替换任何接口。
- REC局部：`F3RootCertificates.lean`，12条定理，REC-L1/L2、单对L4、L11；精确/截断证书正确性，不包括概率或整数素数乘积根构造。
- 全19条新增定理一对一审计；仍须新精确head的构建/回归/公理/源码/覆盖门禁。独立数学源码审阅不替代内核。

## 2026-09-30：实际素数比例与REC局部已核验

代码70becdbf通过push36662676882和PR36662680539完整门禁，620条标准公理声明、96源文件覆盖、既有回归全部成功。DEN-1现有实际全素数计数分母的正层、负层与尾比例，模1PNT与最终非零均已证明；DEN-2原条件17倍比例沿用。REC仅确定性L1/L2、单对L4与L11已证，其余新proof任务继续开放。首轮0cf502e6曾因simp方向/函数商展示/section闭合失败，已作等价语法修复，不改变定理签名或工具链；旧失败不冒充通过。当前文档head另验CI。

## 2026-09-30：RUN 当前主线组合候选

主线 `5a622dc4e90db25dbc21f926de873be17372ed39` 已包含 PR45 的 COR/DEN/LOG、PR46 的真实全素数相对密度与 REC 确定性证书，以及 PR48 的 MULTI 证明边界和 TERN 维数前提修正。当前 RUN 候选保留该主线全部文件，通过三方合并加入五条已有待验证 RUN 接口：625条项目定理加1条上游产生器审计，逐条恰好覆盖。

首次 RUN 冷构建在 BFTExtraction 的巨大符号幂处失败；已仅将该处 `omega` 改为传递性与加法单调性的显式证明，并在完整产生器之前单独验证有限提取模块。全部依赖版本、证明前提和审计允许列表保持原样。修复头 `939f8600f70d97889019cde667a2e24effe3b800` 的 CI 仍在整个私有定理处触发相同巨大幂内核保护；现已将该私有定理全部反射算术换成显式次序证明。本组合仍须新的精确完整 CI，不登记 RUN 完成。

[第三方来源说明](f3_third_party_sources.md) 记录固定来源、署名、许可范围尚未确认及权利人联系后的处理方式。继续技术集成不表示已取得未确认部分的许可，也不降低数学和工程合并门禁。其余已接收 F3 书面证明继续按各结果 ID 推进；原始五目标与新增证明的完整完成尚未达成。

04:01 UTC 已刷新全部162分支及01:58之后更新的issue/PR：仅本任务七个分支、主线和PR42–48发生变化，未发现新的外部证明来源。原始接收水位及声明状态不因刷新而自动升级；详见 `reports/f3_intake_refresh_20260930.json`。


## 2026-09-30：REC-L5 有限矩阵与阈值根簇候选

新增 `OmegaBalance/F3RootReconstruction.lean` 的 10 条声明，基于 master
`5a622dc4e90db25dbc21f926de873be17372ed39` 与既有 `F3RootCertificates.lean`。
完成候选内容：有限列表的首个不等证书、未知的精确刻画、允许根移动但真实距离固定的
扫描正确性/完备性、完整 Option 距离矩阵（无限对角）、真实 p-adic 根的阈值等价关系及
随阈值细化、恢复矩阵的根簇测试和纸面模型包装。精确声明与纸面节点见
[REC 形式化映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l5-有限矩阵与根簇已通过精确-ci)。

外部查重后直接复用 Lean 4.34 `List.findSome?` 的已读源 API、既有单对证书及
锁定 mathlib 的 `Setoid`/`AddValuation` 接口；没有升级工具链或增加依赖。
代码 c2fe3c4 的精确 push36667493101 与 PR36667536541 已全门禁成功：630条标准公理、97文件源码守卫、一对一覆盖及全部回归。REC-L5仅上述确定性矩阵/阈值分区范围已核验；最终文档头另验CI。
没有闭合随机等待时间、联合概率、被动下界、截断矩阵/采样或素数模型传递；
ROOT/PAT/RUN 及其它已接收证明任务的未完成部分保持开放。

## 2026-09-30：REC-L11 / 截断 REC-L5 有限矩阵候选

- 稳定来源：F3-REC-4，proof 定理 2.6（PR #41、b4c14823，proof blob ef55306b）；
  截断矩阵扫描和根簇为 REC-L11 与 REC-L5 确定性方法的组合，不冒称 REC-L12 概率已证
- 恢复基线：master f50d23667628c868610c34d5157fe9bbd21357d3，已含 PR #49 完整精度模块
- 实现：`OmegaBalance/F3RootTruncatedReconstruction.lean`，11 条新定理，
  扫描首个“不等或联合饱和”观测、精确未知条件、移动真实根固定距离下的正确性、
  单对/全矩阵恢复 iff、已知截断对角 H、t≤H 阈值根簇及公共正基础深度的纸面模型包装
- 恢复证据：原本地 e0d7f9c 提交已丢失；244 行源文件按原始写入记录重建，
  blob 4a24db55453664e08976cd883757912c874f1adb 与旧记录相同，文档在最新主线增量接回
- 精确公开声明、前提和节点：[REC 形式化映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l11--截断-rec-l5-有限矩阵已通过精确-ci)
- 查重决定：[外部复用门](f3_external_reuse.md#2026-09-30rec-l11--截断-rec-l5-增量复用门)，
  直接调用已验单对截断证书、锁定 List.findSome? 与现有 Setoid，没有新分析基础
- 恢复后重新执行 source 98 / Audit 641 exactly once / diff 空白检查及有限数学 sanity，
  均通过；随后代码564bb498的push36671721342与PR36671762437实际全门禁成功。仅本批11条确定性定理为已核验，完整REC-4仍未完成；最终文档头另验CI
- 剩余：REC-L3、L6–L10、L12–L13、概率联合深度公式、整数素数乘积根构造、
  固定精度全素数传递；不把有限可观测见证的 iff 解释成随机采样必然完备

原五项目标、其它已接收 proofs、RUN 的无条件产生器和外部证明信任审计继续开放。

## 2026-09-30 05:58 UTC: RUN 恢复与当前主线组合

本轮从远程恢复 RUN 65e0f5e，并真实三方合入 master 8548f385，保留 PR49/50
的全部21条矩阵声明及最新文档。组合候选为646条项目声明及1条必需上游产生器审计，
源文件99个；没有将未验证的 RUN 五条计入 master 已验证641条。

RUN 最新实际CI36671388031已通过 BFTExtraction，但 BFTParameters 两处巨大幂
内核归约失败，后续工程门禁未执行。现以符号参数化小引理修复，保留全部常数、
公开命题与信任门禁；先验两个有限模块，再验完整产生器。15项兼容测试及源码/覆盖
检查通过，新候选仍等待精确 Actions 编译。Haar 概率另在 draft PR51 独立验证，
不把其候选或运行中的CI登记为已证。其余接收清单继续开放。

## 2026-09-30 REC-L3 actual Haar probability candidate

- Source: accepted REC proof §1/theorem2.1 and original shared-product source
  a1a724b6 §3; [exact map](proofs/f3/prime_depth_reconstruction/formalization.md)
- Minimal licensed reuse: [decision and pins](f3_external_reuse.md#2026-09-30-rec-l3-actual-haar-law-target-first-reuse-gate)
- Candidate files: PadicIntHaar / F3UnitHaar / F3RootDepthHaar; concrete normalized
  Haar, actual units of mass2/3, normalized restriction, actual-depth residue
  equivalence including∞, positive single-root tail
- Pending: exact layers, unequal-depth mass, null roots and signed difference,
  original model wrapper, independent waiting-law and prime transfer
- Validation: no local Lean/Lake; source and coverage only until exact-head CI

### REC-L3 extension checkpoint

Candidate files additionally F3RootDepthLaw (8 declarations), F3SharedRootHaar
(6), F3RootDepthNull (3): actual finite shells, unequal-depth mass, unchanged
model wrappers and null root points. All 38 additions to baseline 641 are audited.
Signed Δ, independent waiting/means, full joint law and prime transfer remain open.
First actual CI 8453214e/36675740452 failed on pinned import/complement namespace/
numeral casts; the minimal 5-declaration upstream port compiled. Exact errors fixed
without pin changes; new 38-declaration tree awaits its own full CI.


### 2026-09-30 06:38 UTC intake refresh and actual Haar CI

[Machine-readable refresh](../reports/f3_intake_refresh_2026-09-30_0638.json):
165 actual remote branches checked. All original research heads are unchanged;
changes are confined to master and our ten implementation/correction branches.
Issues updated since 05:02 UTC are PR47, PR50 and PR51. Original mathematical
intake watermarks are preserved; a candidate CI run is not proof acceptance.

The actual Haar candidate at remote f38acf309530f066b5f8340b92e19b48443b81cf
passed compilation of PadicIntHaar and F3UnitHaar, but run36679603580 failed in
F3RootDepthHaar on a cast-lemma name, the modulus-one subsingleton equality and
an insufficiently typed monotonicity cast. The following source fix addresses
these exact elaboration errors without changing statements, assumptions or pins.
The whole 679-declaration candidate still awaits complete exact-head verification.

## 2026-09-30 07:05 UTC：实际 Haar 单次概率内核验证

PR51 代码 dc063232 的 push36681283200 与 PR36681288176 已全部通过：
679 条标准公理声明、104 源文件、精确 Audit 覆盖及全部构建/回归。
六个模块共38条新增声明证明实际单位域归一化、单根尾/层质量、有限根距下
不等深度质量3^-L、原配置包装和无限根点零测。CC0 五声明移植及其全部适配器
现在具有本项目固定 Lean/mathlib 的实际传递公理验证，不再仅为源码兼容猜测。
[精确声明及范围](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30rec-l3-实际-haar-单次概率已通过精确-ci)。
独立等待律/均值、完整有符号差分布、联合恢复概率及素数传递仍未完成；
独立专项源码复核与最终文档头 CI 是合并前剩余门禁。

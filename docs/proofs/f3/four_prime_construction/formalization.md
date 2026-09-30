# F3-PAT-1：形式化映射与阻塞依赖

数学状态：`PAPER-AUDITED`。Lean 状态：`LEAN-IN-PROGRESS`（PAT-L1–3 已通过精确 CI，主结果仍未完成）。PAT-L1–3 已有下表中的 Lean 声明；其余项目仍为目标接口与依赖计划。局部结果不升级全局素数存在性结论。

[定理](theorem.md) · [证明](proof.md) · [引理 DAG](scaffolding.md)

## 1. 已读取的仓库基础

核对基线：`f7033c1625b2fc36d76544488ba0402a0a1619fc`。

- [OmegaBalance/Valuation.lean](../../../../OmegaBalance/Valuation.lean)：`v3 : ℕ → ℕ`、`f3 : ℕ → ℤ`；`valuation_eq_padicValNat`、`v3_eq_zero_of_not_dvd` 等接口。
- [OmegaBalance/F3.lean](../../../../OmegaBalance/F3.lean)：`f3_of_mod_three_two`、`f3_of_mod_three_one`，可以把符号情形化为单侧的赋值。

这里只确认源码接口，不将阅读源码当成此次目标的 Lean 验证。

## 2. 目标模块与声明

建议先新增局部模块 `OmegaBalance/F3FourPrimePattern.lean`；全局模块 `OmegaBalance/F3FourPrimeConstruction.lean` 必须等外部依赖有真实证明后再接入默认 import。

| 书面节点 | 建议目标 Lean 名称 | 目标模块 | 当前完成状态 | 依赖或阻塞 |
|---|---|---|---|---|
| 定义 | `f3Pat1Point`, `F3Pat1Pattern`, `F3Pat1PrimeConfiguration` | F3FourPrimePattern | 已验证（下列精确提交） | 复用现有 `f3`、`Nat.Prime`，形式索引可用 `Fin 4` |
| PAT-L1 | `v3_eq_of_modEq_pow_of_lt` | F3FourPrimePattern | 已验证（下列精确提交） | 已查重，复用 `Nat.ModEq.dvd_iff` 和 `padicValNat_dvd_iff_le` |
| PAT-L2 | `f3_pat1_point_mod729`, `f3_pat1_product_add_one_mod729` | F3FourPrimePattern | 已验证（下列精确提交） | `Nat.ModEq` 与有限系数算术 |
| PAT-L3 | `f3_pat1_pattern_of_mod729` | F3FourPrimePattern | 已验证（下列精确提交） | PAT-L1、PAT-L2、现有模 3 符号接口 |
| PAT-L4 | `f3_pat1_complexity_le_two` | F3FourPrimeConstruction | 未实现 | 需要与外部素数线性形式定理一致的复杂度定义 |
| PAT-L5 | `f3_pat1_local_admissible`, `f3_pat1_singular_product_pos` | F3FourPrimeConstruction | 未实现 | `ZMod` 单位、局部计数、无穷乘积基础 |
| EXT-GT2 | 名称待实际库检索后确定 | 外部依赖 | `BLOCKED-EXTERNAL` | 尚未完成复杂度至多 2 的 Green–Tao 定理的可用 Lean 接口核验 |
| PAT-L6 | `f3_pat1_prime_parameter_count_asymptotic` | F3FourPrimeConstruction | 阻塞于 EXT-GT2 | 真正的全局计数证明 |
| PAT-L7 | `f3_pat1_four_primes_unbounded`, `f3_pat1_four_primes_infinite` | F3FourPrimeConstruction | 未实现且受阻塞 | 无限参数的算术映射、PAT-L3、PAT-L6 |

`BLOCKED-EXTERNAL` 只描述本次工程尚未解决的依赖，不断言整个形式化社区都没有相关结果。书面审计已完成；外部接口核验与目标声明仍待实现，不把计划中的 DAG 当成已完成形式化。

## 3. 必须保留的语义

1. 局部定理保留 `1 < n`、`0 < d`、`n ≡ 5 [MOD 729]`、`d ≡ 1 [MOD 729]`。素数性不是局部定理的前提。
2. 有符号差分在 `ℤ` 内计算；分别 cast 后再相减。不得用自然数减法丢失负号。
3. 纸面定义不涉及零。复用仓库的 `v3 0 = 0` 全函数约定时，必须用正性排除所有邻数零点，不更改全函数定义。
4. 主结论保留可变量 `d`；两个参数同时无界可表为每个自然数下界都有更大的 `n,d`，并保留 `1<n`。
5. `F3Pat1Pattern` 与 `F3Pat1PrimeConfiguration` 分开：七值模式本身不是素数身份。
6. 全局推论使用两个参数的联合素数定理，不能将四次 Dirichlet 定理调用或四个独立存在量词误拼成同一个参数对。

## 4. 外部依赖不能写成数学公理

不得为 EXT-GT2 添加自定义公理、占位证明或 unsafe/native proof escape。若先完成局部部分，必须在结果地图中只报告局部 Lean 定理已完成，主结果仍保留 paper 状态。以外部计数命题作为显式假设证明一个桥接定理，也不等于无条件形式化了 F3-PAT-1。

## 5. 验证登记

| 项目 | 当前状态 |
|---|---|
| 完整书面证明 | 已整理；书面审计通过 |
| 对既有提交的书面审计 | 已完成；对象与范围见 [审计记录](scaffolding.md#5-书面审计记录2026-09-29) |
| Python 有限复核 | [报告](../../../../reports/f3_pat1_paper_check.json)；不承担无限证明责任 |
| 新增 Lean 声明 | 3 个定义、4 条 theorem；局部代码 head `5f94116a7bddd73b37ebf4634a8d71f16ff54fe9` 已验证 |
| 当前主结果的 Lean 核验提交 | 无 |
| 当前主结果的内核公理审计 | 未运行 |
| 本轮 `python3 scripts/verify.py` | 已执行；本地缺少 `lake`，退出码 2，未进入 Lean 构建 |
| 提交的仓库 CI | 在 PR 中记录精确 head 与运行链接；不作为本主结果的 Lean 证明 |

以后每条新增 Lean theorem/lemma 都须登记 `scripts/Audit.lean`，完成构建、回归、公理、源码及覆盖检查。只有同一精确 Git head 通过完整门禁，才能将主结果标为 `LEAN-PROVED`。本轮新增 `F3FourPrimePattern.lean` 并接入默认 import 与一对一审计；工具链和依赖版本不变。

查重证据见 [外部复用记录](../../../f3_external_reuse.md)，接收及任务状态见 [持续任务清单](../../../f3_formalization_tasks.md)。PAT-L1 显式要求两个赋值参数非零，防止总化零点破坏结论。

## 2026-09-30 局部代码验证

代码提交 `5f94116a7bddd73b37ebf4634a8d71f16ff54fe9` 的 [push Lean run 36658263293](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36658263293) 与 [PR Lean run 36658302054](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36658302054) 均成功。构建、三组回归、公理、源码、覆盖及有限检查全部通过：286 条声明一对一审计，30 个 Lean 源文件无禁用项，144240 项有限回归。两条模类定理仅依赖 `propext`；赋值稳定性及七值定理仅依赖标准 `propext`、`Classical.choice`、`Quot.sound`。

这是 PAT-L1–3 的 `LEAN-PROVED` 证据。F3-PAT-1 主结论仍为 `PAPER-AUDITED`、Lean `IN-PROGRESS`；PAT-L4–7 与 EXT-GT2 未完成。此记录之后的文档提交仍须独立精确 CI，不把旧运行算新 head 的检查。

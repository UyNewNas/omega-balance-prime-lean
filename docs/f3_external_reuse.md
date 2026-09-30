# F₃ 外部查重复用记录

本记录区分源码核验、外部构建报告与本仓库精确提交的内核验证。未找到表示下述已查范围内未找到；访问失败不表示定理不存在。

## 2026-09-30：F3-PAT-1 局部算术（PAT-L1–3）

- 本仓库基线：`b4c14823d9a97a45770ed42379673d39b5295be6`；证明来源：`4c532a866ad60bbe0492a928b41fe1fa1c1766e6`，后续 PDF 整理不改变局部结论。
- 目标：对 `1<n`、`0<d`、`n≡5,d≡1 (mod 729)`，四点值 `(1,-1,-1,-1)` 与三个乘积值 `(3,5,3)`；无素性假设，也不作全局素数存在性推论。
- 锁定 mathlib：[`5ed2965256430c3649e86755f9576b54eca72435`](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435)，Lean `v4.34.0`。已读取实际声明及证明体，许可证为 Apache-2.0。
- 查询：GitHub `padicValNat mod`、`padicValNat eq_of`、`valuation add_eq_min`、`map_add_eq_min`、`f3_pat1_pattern_of_mod729`；锁定源码与当时最新主线 `a79b0d211ae2978372e1408be7162e0710f589da` 对照。最终七值定理在已查范围未找到现成实现。

| 缺口 | 已核验复用源 | 前提与决定 |
|---|---|---|
| 同余传递整除 | [`Nat.ModEq.dvd_iff`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Nat/ModEq.lean)；blob `89b9538904c468cdd94f8cd1613fb1fea8c9700d` | `a≡b [MOD m]`、`d∣m` 给出 `d∣a ↔ d∣b`；直接复用 |
| 幂整除与赋值 | [`padicValNat_dvd_iff_le`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean)；blob `09e4fe43670b683a56a386ff184228b0894fe2d3` | 素数实例及非零输入；直接复用，不能对总化零点遗漏前提 |
| 项目赋值桥梁 | `valuation_eq_padicValNat` / `v3_eq_padic` | 保留项目 `v3` 定义，仅薄适配 |
| 符号与有限运算 | 项目 `f3_of_mod_three_one/two`、mathlib `Nat.ModEq` 运算 | 补未覆盖局部组合；不引入新依赖 |

本地未安装 Lean/Lake，构建、公理传递闭包及回归由现有 GitHub Actions 的精确提交验证。源码读取及有限检查不是内核验证；状态以 PR 的精确 SHA 与运行链接为准。

## 2026-09-30：PAT 全局依赖边界

查找最终等价目标优先：GitHub `Green Tao`；网络/社区 `Lean formalization linear equations in primes`、`Lean Green-Tao formalization`、`site:leanprover.zulipchat.com Green Tao primes`。已查范围未核验到可访问、可重用的 GT10 Corollary 1.7 复杂度至多 2 素数线性形式渐近的完整 Lean 源码。

[`lean-eval-submissions/results/vilin97.json`](https://github.com/leanprover/lean-eval-submissions/blob/main/results/vilin97.json) 记录任意长素数等差数列的接受结果，包括 `Vilin97/lean-eval-green-tao@0c5d3337c3ebb59c318ab9030e31b835826141f8` 与 `AxiomMath/lean-eval-submissions-final@b092f7455ac0cf0c405e42fbb669ef8144de9fd9`，但标记 `public:false`；前者源码读取返回 404。源码、许可证、精确前提和传递信任未能核验。任意长等差数列也不自动给出本项目指定同余条件的二参数渐近。

决定：保持 EXT-GT2 为外部未解决依赖；不添加文献公理或同名假设，不将 `PAPER-AUDITED` 降称猜想，也不将局部模式称为主结果 `LEAN-PROVED`。先形式化已核验复用范围内的 PAT-L1–3。

## 2026-09-30：复用已验证 COR / DEN / LOG 栈

最终目标优先检查开放 PR 的真实声明，避免重复实现：本仓库 [PR #28](https://github.com/UyNewNas/omega-balance-prime-lean/pull/28) 的固定源 `66b8e8380d240868c5fdd784eeb6aedb966cae3a` 已有完整整数相关极限、正幂三平移均方极限、正负素数密度与17倍升层比例、真正三进 log 级数及同态/赋值桥梁。读取了实际 Lean 定义、假设和证明体；不是以 PR 标题或旧任务状态作证据。

源版本 [Lean run 36309723481](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36309723481) 成功，597 条声明公理/覆盖通过，93 个项目文件无禁用项。该运行只证明源版本，不能代替当前 master 合并后的验证。

采用真正三方合并，保留 master 新证明包、PAT-L1–3、ROOT-4 修正；仅 import/Audit/任务账本冲突作并集处理。锁定 Lean/mathlib 不变，ANT 使用原源固定 `099d3726c2c74841024110ec1dd9902f7ef36e9e`；不改上游仓库。新组合树要求重新构建全部 601 条声明并核对实际解析依赖清单。已验证历史 API 保留。

RUN 的有限 CRT、最大化、顺序块和条件组合接口一并保留，但无条件素数产生器仍未完成。PR #29 固定 `9033636693d0f713c9cb6e1bc5d13149052b812b` 的 [Lean run 36467303064](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36467303064) 构建失败：`lean-proofs-latest` 与 `analytic_number_theory` 重复模块所有者，以及锁定版本的 Sobolev/BoundedGaps API 不兼容；下游回归和公理检查未运行。该失败栈不导入本次组合候选，不以文献公理或新增假设填补无条件 RUN。

源 CI 解析依赖已从成功 run `36309723481` 的 artifact `10929140097` 下载，ZIP SHA256 与 GitHub 报告一致：`31e70f907bde8c1e375f5acfd3384771d616249091a7f45c68fbb685e21cc0e1`。本次提交该实际 `lake-manifest.json`：mathlib `5ed2965256430c3649e86755f9576b54eca72435`、ANT `099d3726c2c74841024110ec1dd9902f7ef36e9e`、LeanArchitect `78dd66840d3efe8c824c699fc03381cec817c271`、Cli `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`；其余传递固定版本按完整清单保留。不是手工猜测 Lake 的解析结果。ANT 原源使用4.33rc1/mathlibe4c91783，但上述消费端4.34/5ed组合已有真实编译证据；当前组合仍待新CI。ANT许可证Apache2，依赖源码闭包审计继续独立记录。

ANT源闭包复核完成：从`PrimeNumberTheoremAnd/Consequences.lean`递归到9个本包模块，379391字符；使用本仓库支持嵌套注释与字符串擦除的禁用项扫描，0命中。范围排除锁定Mathlib、Architect及Batteries的实现源码。WeakPNT_AP的前提仅q≥1、a.Coprime q、a<q，不含目标重述假设；最终COR/DEN/LOG声明在历史成功日志中逐条只依赖标准3公理。证据摘要见`reports/f3_ant_source_scan.json`；本组合CI仍会实际执行全601条公理审计。

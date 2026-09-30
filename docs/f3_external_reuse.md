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

## 2026-09-30：相对全部素数计数与 REC 确定性证书

密度最终目标先查：GitHub `f3PrimePosLevel relative density` 在已查范围无匹配；本仓库所有分支标题/现有API核对后，仅17倍接口已用实际计数比。薄复用既有 `f3PrimeAPCountingReal_normalized_tendsto` 的模1特化（0与1互素）得到真实全素数计数PNT，复用 `Filter.Tendsto.div` 及 `div_div_div_cancel_right₀` 将三个x/log x极限转换为实际素数计数比例，无新分析栈。

锁定mathlib5ed2965实际源码：`Mathlib/Topology/Algebra/GroupWithZero.lean` blob `ad409ad08d53ad030bfd8f29cb2825a19b33872e` 的 `Filter.Tendsto.div` 要求分母极限非零；`Mathlib/Algebra/GroupWithZero/Units/Basic.lean` blob `b3148d9bd8bac8cbc1c64edf40b1c0bbb61f2916` 的商约消要求公共除数非零。已分别读完整声明及证明，最新默认源同API仍在（blob4ef88673与9fd9e942），不升级。通过PNT极限1证明分母最终非零，有限初段不强加全局假设。库为Apache2，当前代码独立CI待执行。

REC最终目标在已查GitHub精确名 `rootDepth_min_eq_distance_of_ne` / `truncatedDepthCertificate_sound` 无匹配；直接复用锁定 `AddValuation.map_sub`、`map_add_of_distinct_val`、`map_neg`、`map_sub_swap`、`top_iff`/`ne_top_iff`（`Mathlib/RingTheory/Valuation/Basic.lean` blob73f71ae8fde499401b25db33fd2d826eecfb9c0b），以及真正 `Padic.addValuation : AddValuation ℚ_[3] (WithTop ℤ)` 和 `.apply`（PadicNumbers blob79040472922216be2c0d66793e3b2a3965347e9c）。有限精度只用 `Mathlib/Order/MinMax.lean` 的已读 `min_lt_min_left_iff`、`min_eq_right_iff`。保持∞零点、实际p-adic域和源模型b+R；不以有理数弱化或概率假设代替目标。

## 2026-09-30：REC-L5 目标优先查重复用

目标先固定为命题 2.2 的**确定性有限观测矩阵恢复和阈值根簇**，不是采样律、
信息论下界、全素数传递或重新开发 p-adic 赋值。源码基线 master
`5a622dc4e90db25dbc21f926de873be17372ed39`；paper proof 最后数学来源提交
`b4c14823d9a97a45770ed42379673d39b5295be6`（PR #41），proof blob
`ef55306b0c00adc68cfd8407440a4bdd46e6de10`。本轮完整重读 theorem/proof/scaffolding/formalization。

实际查询（2026-09-30）：GitHub code `rootDistanceMatrix depthCertificate`、
`rootClusterSetoid depthCertificateMatrix`、`ultrametric equivalence Setoid`、
`findSome? eq_some`、`ultrametric root recovery`；mathlib PR `ultrametric reconstruction`；
全局 PR `p-adic root cluster matrix reconstruction`；公开网页
`Lean ultrametric reconstruction root distance matrix valuation certificate`、
`Lean mathlib ultrametric Setoid balls equivalence relation`、
`"Corregidor" "Martínez-Pérez" "Lean"`。已查范围未找到等同最终 F3 目标的 Lean 定理；
无关数值根隔离代码与非 Lean 材料不是可复用证明，不作全网不存在声明。
书面引用 [Corregidor–Martínez-Pérez, arXiv:2003.10239](https://arxiv.org/abs/2003.10239)
已核对论文入口；一般 metric-basis 背景不替代本目标源码证据。

直接复用/薄适配清单：

| 来源、固定版本、源码证据 | 精确 API 与适配决定 |
|---|---|
| 本项目 `OmegaBalance/F3RootCertificates.lean`，PR #46 已验代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b` | 复用 `depthCertificate_sound`、`rootDepth_min_le_distance`、`rootDistance_ne_top`；既有 12 个证书定理保持不变，不复制不重证 |
| [Lean v4.34.0 `Init/Data/List/Find.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Find.lean)，blob `d8c0b839d8f24f52d21d7a0f34a5be621894dff8` | `List.findSome?`；`List.findSome?_eq_some_iff` 给出首个成功观测和之前全为 none 的前缀；`List.exists_of_findSome?_eq_some` 提取真实成员；`List.findSome?_eq_none_iff` 刻画未知。实际读取精确声明及证明；直接应用，不新增递归扫描基础 |
| [mathlib 5ed2965 `Data/Setoid/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Setoid/Basic.lean)，blob `90500f54e13f5572f222575d910bdccbbd4dd3ed` | 用原生 `Setoid` 表示根簇分区，用其关系包含顺序表达高阈值细化；不新建通用分区/树框架 |
| [mathlib 5ed2965 `RingTheory/Valuation/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/RingTheory/Valuation/Basic.lean)，blob `73f71ae8fde499401b25db33fd2d826eecfb9c0b` | 直接用已读 `AddValuation.map_zero` 和 `map_sub_swap`，传递性复用项目中实际 `Padic.addValuation` 的最小值界。保留 `WithTop ℤ` 及命中根时的 ∞ |
| [mathlib 5ed2965 `Topology/UniformSpace/Ultra/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Topology/UniformSpace/Ultra/Basic.lean)，blob `9a201e0bc4fc8412b18b6f3f6ca5fce0131d6d26` | 阅读完整文件：通用超度量一致空间 API，仍注明 valued-ring 超一致性桥接 TODO；不导入该较大拓扑接口来包装三个初等关系律 |

实时核对上述 Lean `Find.lean` 与 mathlib `Ultra/Basic.lean` 的最新默认分支，返回 blob
与所查锁定版本相同；已查 mathlib PR 无等同目标候选。库源码为 Apache-2.0，
当前只调用原依赖的接口，没有移植外部证明文件或增添新包。最终声明的定义域为真实
`ℚ_[3]`；一般适配器允许任意 p-adic 点，纸面 wrapper 显式保留 `F3SharedRootConfig`、
样本为单位、固定基础深度及逐对真实根距固定。没有假设扫描所得矩阵等于目标，
没有将单位域概率律写作前提。

结果：`F3RootReconstruction.lean` 的 10 条新声明待精确 head CI；本地 source/coverage
检查通过（97 文件、630 条一对一），本地无 Lean/Lake，未执行内核或实际公理输出。
[完整映射与剩余项](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l5-有限矩阵与根簇候选尚未执行-lean)。

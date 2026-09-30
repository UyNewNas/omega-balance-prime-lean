# F₃ 全量形式化任务清单

## 2026-09-30 11:47 UTC：实际有限批次截断矩阵尾界已通过精确 CI

代码95c32fe0de79502fba19972d86d327c32103eaf6，树647521f257918a7625542896e07ef320a7dae25f，
[push36710285308](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710285308)与
[PR36710327735](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710327735)
首轮完整成功。11条新声明仅标准公理（证书对称引理不依赖任何公理）；764项总输出
（763项目+1产生器）、113项目源文件、650依赖模块及版本锁、构建、内核回归、一对一
覆盖和144240有限检查通过。测试PR合并树与上述源码头的文件树相同。

已覆盖REC-L12/定理2.6式(2.14)：真实有限单位Haar乘积采样下，既有截断矩阵算法
未恢复min(L,H)的概率≤min(1,choose(m,2)·exp(−T/(2·3^(H−1))))。对角线H、联合饱和、
命中根原深度∞和T=0保留；时间乘积与根对并集分别证明，没有根对独立性假设。
连同已验单次式(2.13)，当前覆盖原固定模型的两条截断概率公式及实际算法事件。

84个有限案例45143批次（含16636根命中批次）只是补充回归。独立数学/源码复核
通过；有限精度不可辨识的完整分布声明、移动配置和全素数传递仍开放，不能把整个
定理2.6或REC包全部标成完成。此状态文档头不变更已验代码/审计，仍另行完整CI。

## 2026-09-30 11:23 UTC：单次截断证书 Haar 分段律已通过精确 CI

代码94bc0693b5c1bfca7d054d20daf9efea00a0b67a，树9ba2bea3889e77d85a63fcf3c86d3f27b51d0250，
[push36707863669](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707863669)与
[PR36707908267](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707908267)
首轮完整成功。12条新声明仅标准公理；全753项公理输出（752项目+1产生器）、112项目
源文件、650依赖模块及版本锁、构建、内核回归、精确覆盖和144240有限检查通过。

已覆盖REC-L12/定理2.6式(2.13)的实际单次概率：L<H时证书事件等于原不等深度事件，
质量3^(−L)；L≥H时等于真实共同H球，质量1/(2·3^(H−1))，包括L=H。另有可测性、
实际事件包含给出的统一下界、原固定配置包装。H截断标准化R，命中根∞保留至截断，
恢复目标仍为min(L,H)。高距离一般引理允许更广根域，但最终包装保持原C全部前提。

30个精确有限剩余类案例6564次观测含60次根命中只是补充回归；H=0反例说明为何质量
公式要求H≥1。独立源码/数学复核通过。式(2.14)的有限批次截断矩阵尾界、移动配置、
全素数传递与整个REC包仍开放。此状态文档头不变更已验代码或审计，仍单独执行完整CI。

## 2026-09-30 11:04 UTC：实际完整矩阵置信保证已通过精确 CI

代码361cdd3c958897b342297dfbc7abb55a66e3a4cb，树6979590446d56975243dd667081e37c40542456f，
[push36705872257](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705872257)和
[PR36705919682](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705919682)
首轮完整成功。三条新声明仅标准公理；全741项公理输出（740项目+1产生器）、111项目
源文件、650依赖模块及版本锁、构建、内核回归、覆盖和144240有限检查全部通过。

对原固定配置、0<δ<1和自然T≥3^K log(choose(m,2)/δ)，真实单位Haar流前T次观测使
原证书矩阵恢复全部真实距离的概率至少1−δ。成功事件通过已有逐点矩阵等价和可测尾
补事件证明，不预设目标概率；K为实际根距最大值，根命中∞及真实∞对角线保留。

与先前已验标量尾律/期望、联合尾界/对数期望一起，覆盖纸面定理2.3在固定原局部模型
中的式(2.7)、式(2.8)及其显式置信推论。整个REC包仍未完成：截断概率、移动配置、
全素数传递、有符号差律、被动下界和三等距根精确停止律等继续开放。36个数值阈值与
8个有限根模型有理成功概率仅为回归。独立数学/源码复核通过；此状态文档头仍另行
执行完整CI。原始proof来源水位保持不变。

## 2026-09-30 10:47 UTC：REC-L7 实际联合等待对数期望已通过精确 CI

代码1b9a0d63b4c2be6d063dda68a60f1ceffa7cf130，树de59e407b238b301cafa9474a4babeb9cb553d58，
[push36704236926](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704236926)与
[PR36704245738](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704245738)
完整成功。12条新声明仅标准公理；全738项公理输出（737项目+1产生器）、110项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查全部通过。

REC-L7/定理2.3式(2.8)的实际最大等待时间满足原精确上界
Eτ≤1+3^K(1+log choose(m,2))，这里期望是保留∞的真实非负积分，K为实际根距最大值。
已证明真实最大等待几乎处处有限，原有证书矩阵几乎处处在某个有限T恢复全部真实距离。
证明调用锁定库的指数积分/积分判别和已验真实联合尾界；没有预设分布或根对独立性。

首轮编译的默认有限区间质量、反单调限制集参数、Nat索引/局部常量展开及符号归一化
已显式修复，12个公开命题及全部前提保持不变。294个浮点解析前缀与28个有限样本尾和
仅为补充回归。显式置信参数δ推论、移动配置、完整有符号差律和素数传递仍开放。
本次状态文档头保留全部已验代码和审计，仍独立执行完整CI。原纸面来源水位不变。

## 2026-09-30 10:12 UTC：REC-L7 实际联合停止尾界已通过精确 CI

代码0324861a6b94294421d692203e8847802b1044f4，树dbbe7e42a1c38aff722b05568ca5c9a957fe69dd，
[push36700614557](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700614557)和
[PR36700618251](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700618251)
均完整成功。14条新声明逐条仅依赖propext、Classical.choice、Quot.sound；全726项
公理输出（725项目+1必需产生器）、109项目源文件、650依赖模块及固定版本、完整构建、
内核回归、覆盖和144240有限检查通过。

已验范围是REC-L7/定理2.3式(2.8)的尾界部分：固定原配置的真实一基最大等待时间，
按i<j恰计choose(m,2)对，K为这些实际有限根距的最大值；逐点证明τ≤T等价于原证书
矩阵恢复全部真实根距，保留∞对角线、命中根和T=0。真实单位Haar无限流的尾概率
不超过min(1,choose(m,2)·exp(-T·3^-K))，仅使用对之间并集界，不假设根对独立。

首轮编译失败已作四处语法/推断/存在量词归一化修复，14条公开命题及模型前提不变。
185653个有限批次（含27607个命中根批次）只是补充语义回归。对数期望界、移动配置、
完整有符号差律及素数传递仍开放，不把尾界当作这些结论。本次状态文档头还需独立完整CI。

## 2026-09-30 09:40 UTC：实际固定根等待律已通过完整内核验证

代码0255c6b55f44ecb2fc7ee69a376969f655ac4e83，树3430edd9b9f09b4663e6018c8ec07a72b8c1d07e，
[push36697262997](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697262997)和
[PR36697267202](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697267202)
均完整成功。12条新声明分别输出仅propext、Classical.choice、Quot.sound；全部712项
公理输出（711项目+1必需产生器）、108项目源文件、650依赖模块、固定版本、构建、
内核回归、一对一覆盖及144240有限检查通过。独立数学/源码复核和主线保留复核通过。

新增证明对应REC-L6/定理2.3式(2.7)的固定根及固定原配置部分：真实无限单位Haar流上，
一基首次证书时间（从不命中仍为∞）满足实际几何尾律，非负期望3^L，并且几乎处处有限。
逐点尾计数包括∞，没有用预设概率质量替换采样空间。实际原配置保留共同正基深度、
m≥2、互异同模3单位根；截断/联合矩阵停止界、移动配置、有符号差律和素数传递仍未完成。

前三轮编译失败属于类型包装/命名/API匹配：最终使用ENat专用递归、显式类型及
库hittingAfter等价的直接命题组合，避免重写器展开p-adic包装。没有改动公开结论或
前提，也未增加透明度/安全设置。以上是已验代码；本次状态文档头仍另行运行完整CI。

## 2026-09-30：实际一基等待时间候选（固定根）

本候选基于已验证批次主线33ccdfe，新增 `F3RootWaitingHaar.lean`。
`f3UnitHaarStream` 是实际 `Measure.infinitePi` 单位 Haar 乘积；
`f3RootWait` 是对真实“不等深度”事件调用库的 `hittingAfter`，从下标0开始再加1，
值域 `ENat = WithTop Nat`。从不出现证书时仍为∞，没有通过 toNat 把∞改成0。

候选逐点证明 T<τ 等价于前T次全部失败，包括T=0；把该事件识别为实际有限柱集，
再由已有单次Haar律计算几何尾概率。τ本身逐点等于尾指标的非负级数，包括∞情形；
可测性、非负积分交换和库几何级数给出实际期望 `∫⁻τ=3^L`，再推出几乎处处有限。
没有预设几何分布、概率公式或同次观测的根标签独立性。

纸面映射：REC-L6 / 定理2.3式(2.7)的固定根与固定原配置部分。
此处没有证明移动随机配置、联合矩阵停止界、完整有符号差律、被动下界或素数传递。
原配置包装保留正b、m≥2、互异同模3单位根；观测为超额深度R。

代码和12个Audit条目目前为未编译候选，本地源码107文件、706条项目声明+1产生器
覆盖检查通过，不能替代精确CI。有限二元前缀回归共1533个带权样本，验证一基计数、
T=0、从未命中的有限前缀语义、几何尾及截断期望；不是无限采样证明。
最终接入最新主线及新的完整Actions门禁仍是接受条件。

## 2026-09-30 09:03 UTC：WAV 短窗口修复已通过精确内核验证

代码 `c7e5d7d55209e575cc1449cf4595762f63469cf2` 的
[push 36690453078](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690453078) 与
[PR 36690460110](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690460110)
全部成功：700项公理审计（699条项目声明+1必需产生器）仅含标准公理，
107个项目源文件、650个依赖模块及固定版本检查、完整覆盖、构建和回归均通过。
一般非整除引理与四个边界回归均有实际公理输出；独立数学/源码复核通过。

只升级 `F3-WAV-1-PROOF-BOUND`：严格窗口的整数判别式非整除、r=2/h=10旧大小界
反例及其正确结论、h=2零判别式、h=25排除端点的精确整除层/权重回归。
不宣告整个条件传递或WAV2–6已形式化，不把源PAPER-AUDITED归属解释为本次全包再审计。
首轮未限定dvd_sub的失败已据固定Lean4.34 API改为Int.dvd_sub，公开命题没有改变。

最终树另合入已验缓存工作流主线ef68dc4，数学源码与上述已验版本字节相同；
仅更换缓存保存范围，所有内核/源码/公理门禁保留。这个组合/文档头仍单独执行CI。


## 2026-09-30: F3-WAV-1-PROOF-BOUND code candidate

Only the accepted paper proof's short-window discriminant step is repaired and
implemented: integer `h`, natural `r≥2`, and `2<h<3^(2r−1)−2` imply
`3^(2r−1) ∤ h²−4`. `OmegaBalance.f3Wavelet_discriminant_not_dvd` uses the two
positive factors, their difference 4, and existing mathlib prime-power APIs.
It does not use the false whole-discriminant size bound. Four kernel regression
candidates cover `r=2,h=10` as a counterexample to that bound, its valid
nondivisibility, `h=2`, and the first excluded `h=25` with weight `−1`.

Status: **CODE-CANDIDATE / EXACT-HEAD-CI-PENDING**, not LEAN-PROVED.
Source guard (106 files), one-to-one Audit (689 project + 1 external), six
coverage tests, and 199262 finite interior checks pass; Lean/Lake is absent and
`verify.py` stops before kernel work. Fixed toolchain and all public hypotheses
remain unchanged. Full F3-WAV-1 conditional transfer and F3-WAV-2–6 remain open.
The source package has no PDF/TeX and this repair makes no render claim.
[Mapping](proofs/f3/wavelet_transfer/formalization.md),
[exact source correction](../reports/f3_wavelet_bound_correction.json),
[reuse gate](f3_external_reuse.md#2026-09-30-f3-wav-1-proof-bound-target-first-reuse-gate).


## 2026-09-30 08:17 UTC：固定根有限批次概率已通过精确 CI

代码 `c863b99d1ba71c4a63e9b555e36bb457e0918bef` 的
[push 36684973082](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36684973082) 与
[PR 36685062948](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36685062948)
全部通过。实际公理日志为695项（694条项目声明+1条必需上游产生器），仅标准三公理；
106个项目源文件、650个依赖源码/固定版本检查、一对一覆盖、内核回归、
144240有限检查均成功。独立专项源码/数学复核确认实际归一化 Haar、真实有限乘积、
共享单次参数、T=0及既有扫描接口，没有循环概率假设。

本节只升级 `F3RootBatchHaar.lean` 已列出的10条声明，得到固定实际单位根的
有限批次失败/扫描未知概率 `(1-3^(-L))^T`。原始完整配置的固定模型包装保留全部
前提和无限根点；未构造无限单边等待变量、未证明其均值、移动随机配置、
多对联合恢复界或素数传递。此前 candidate/pending 文字是实现历史。
最终文档提交仍单独执行完整CI，原始 proof 来源水位不因本次实现而改变。


## 2026-09-30 07:30 UTC：当前状态（优先于下方历史检查点）

PR #47 已合入 master `0bd5333e92b429306ffb139728c04cd4a1ee796b`，其树
`a0109985e1258d4f5a4ade5286865166f8550f28` 与组合验证
[push 36683223631](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36683223631) /
[PR 36683404748](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36683404748)
完全相同，两次全门禁均成功：684 条项目声明与1条必需上游产生器。
原五项目标 INF/COR/DEN/LOG/RUN 已集成主线；全部接收 proof 的其它任务继续开放。
合并后 master 的 Factor-sum 36683869677 已成功，Lean 36683869679 在本检查点仍运行，
不把运行中状态记为成功。下方“待组合/待合并/仍阻塞”等段落均为各日期的历史记录，
不能覆盖本节当前状态，也不能把原五项目标完成误读为全部新 proof 已完成。

07:28 UTC 全量 fetch 后的有界接收刷新检查了165个远程分支头：原始来源中仅 master
变为0bd5333，原始 research 分支头全部未变；06:38后更新的 issue/PR 仅本任务PR47/51。
这次07:30刷新未发现新的外部纸面来源，不推进原数学来源水位，不声称重新全文审读
所有 research。REC 当前批次另完整重读了其既有四文件包。

### 当前新候选：REC-L6 固定根有限批次（待精确 CI）

`OmegaBalance/F3RootBatchHaar.lean` 新增10条定理：在实际
`Measure.pi (fun _ : Fin T => f3UnitHaar)` 下，固定实际单位根的全部T次相等事件
概率为 `(1 - ((3 : ℝ≥0∞)^L)⁻¹)^T`；真实根距有限且L≥1，T允许0。
同时证明事件可测、空批次边界、现有 `depthCertificateScan (List.finRange T)`
返回未知的精确事件等价及概率，并保留固定 `F3SharedRootConfig` 包装。
每个观测只抽取一个d供所有根标签共享；没有假设同次观测内部标签独立。

本地源码守卫106文件、694+1一对一覆盖、15项兼容测试、6项审计规则测试、
11项既有边界测试和333738个有限批次/24组精确分数sanity均通过。
`python3 scripts/verify.py` 因没有Lake以退出码2停止，Lean构建/内核回归/实际公理
检查未运行；这些新声明全部为LEAN-IN-PROGRESS，须新精确head完整CI后再提升。
[精确声明和纸面映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l6-fixed-root-finite-batch-candidate)
· [目标优先复用证据](f3_external_reuse.md#2026-09-30-rec-l6-finite-batch-target-first-reuse-gate)。

边界：本轮仅证明式(2.7)的固定根有限批次失败律，没有定义无限流中的一基等待时间
或求其期望；移动随机配置、无序多对并集界、完整联合分布、被动下界、截断概率、
素数乘积根构造与素数采样传递仍开放。没有新增概率框架或改变固定依赖。

## 历史检查点：2026-09-30 07:16 UTC 无条件 RUN 与主线组合

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

## 历史组合验证（2026-09-30，当前状态见本页顶部）

代码head `febe6175d83d8f2fa92b6f8a3d2b610016119a22` 完整601条门禁通过（PR run36660504382、push run36660499386）。COR-1/2与LOG-1已经非条件证明；DEN实际层计数的x/log x归一化渐近及17倍条件比例已证明，显式相对全部素数计数的3个比例接口仍待补。无条件RUN-1/2仍受产生器兼容阻塞；原有条件RUN接口不冒称完成。PAT-L1–3已合入，所有已接收新proof的未完成局部/全局节点保留在接收账本，不因前三项目进展而关闭总任务。

合并差异专项复核：旧栈66b8e838的91个OmegaBalance源码blob逐一保持；根import为两侧并集88项，Audit为两侧并集601项，无重复/遗漏，最新master文件零丢失。实际manifest与历史成功artifact字节一致；新组合已真实编译和公理复验。当前文档提交仍独立检查后方可合并。

## 固定边界

- namespace：`OmegaBalance`。
- Lean 4.34.0；mathlib 固定提交 `5ed2965256430c3649e86755f9576b54eca72435`。
- 每条项目 `theorem` / `lemma` 必须在 `scripts/Audit.lean` 恰好登记一次。
- 禁止 `sorry` / `admit`、自定义数学公理、unsafe/native proof escape、同名假设伪装结论或削弱前提。
- PR #5 是独立的质因数求和研究线；F₃ 推进不覆盖其分支。
- 最终状态以精确 GitHub Actions head 或相同 Git tree 的成功门禁为准；运行中的 CI 不登记为通过。

## 历史总目标快照（当前集成状态见顶部）

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

## 2026-09-30 08:30 UTC：WAV 精确 API 修复与当前主线组合

首个实际 PR run36686787116 在 F3WaveletLocal 第30行报告未找到未限定的
`dvd_sub`；并未通过内核门禁。源码已仅改为固定 Lean4.34 的 `Int.dvd_sub`，
其精确声明位于 src/Init/Data/Int/DivMod/Lemmas.lean:54–55，
blob99da2d83e13e782fb6ab3304b39321ded95e3737。公开命题、窗口及其余证明保持原样。
同时真实三方接入已验批次主线33ccdfe，保留全部10条新 Haar 批次声明和现有文档；
组合候选为699条项目声明+1条必需上游产生器，107个源文件。
新组合仍需精确CI，不能把源码/覆盖通过或旧基础CI当作WAV内核证明。

## 2026-09-30 09:23 UTC：等待时间首轮 CI 诊断与主线组合

候选0b80102d的push36691409632和PR36691460119均在新等待模块失败；实际RUN产生器
已构建，但后续公理/回归/覆盖门禁未完成，不能据此认定等待律已证明。固定版本中ENat
是WithTop Nat的类型定义而非可自由混用的缩写；修复将实际hittingAfter结果显式标成ENat，
使用ENat专用recTopCoe及自然数嵌入比较API，并调用实际常函数指标的积分变体。
所有公开结论、无限值、原模型及概率前提不变。

同时真实三方接入主线7d94cf69，完整保留已验WAV五条声明与默认分支缓存保存工作流。
组合源码108文件、711条项目声明+1必需上游产生器的一对一覆盖及六项审计规则测试通过；
这些只是预检，组合仍须新的精确CI。09:11读取169个实际远端分支并检查近期PR/issue，
原研究来源头未变，新增记录仅为本轮工程PR；不更改原始proof水位或提升未验任务状态。

## 2026-09-30：REC-L7 实际联合停止尾界候选

- 来源：已接收REC纸面包，PR41 / `b4c14823d9a97a45770ed42379673d39b5295be6`；
  theorem 2.3式(2.8)尾界，稳定节点REC-L7，依赖REC-L6等待律与REC-L5矩阵扫描。
  本轮再次读取完整theorem/proof/scaffolding/formalization，不新增来源水位。
- 基线：PR54合入 `338442744c906dae107b65e83f010f0b76d71ad2`。
- 实现：`F3JointWaitingHaar.lean`，14条声明，见
  [双向精确映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30rec-l7-实际全矩阵停止尾界候选)。
  原配置全部前提保留；实际canonical i<j最大等待、真实最大有限根距K、τ≤T iff既有
  首T次矩阵扫描恢复、choose-two有限并指数尾界；不引入根对独立性或待证概率假设。
- 验证：本地109源文件、725项目+1外部产生器精确覆盖、6审计/15兼容/11边界测试通过；
  185653个有限批次、28情形sanity通过。未执行本地Lean，精确head Actions待父任务运行。
  这些源码/有限检查不升级为LEAN-PROVED。
- 后续：编译并修复当前候选，精确树所有门禁通过后仅升级覆盖尾界。对数均值、置信参数
  推论、移动配置、截断等待、三根精确停止律、素数传递均仍开放。

## 2026-09-30：REC-L7 实际最大等待期望候选

在已验联合尾界主线ee288806上新增F3JointWaitingMean.lean的12条候选声明。
直接积分已有真实ENat最大等待时间，保留从不命中的∞；逐点尾计数、可测性和非负积分
交换后，用已验实际尾概率控制期望。解析部分调用锁定库的递减函数积分判别、指数
可积性及不定区间积分，将min(1,B exp(-px))在log(B)/p处分割并分别上界，得到
原纸面精确上界1+3^K(1+log choose(m,2))；不是替换成较弱常数或预设几何分布。
进一步候选推出最大等待几乎处处有限，以及原证书矩阵几乎处处最终恢复。

固定原配置C的全部正基深度、m≥2、互异同模3单位根前提保留，K仍为实际有限根距最大值。
本候选尚未编译：源码110文件、737项目声明+1产生器覆盖及6项审计规则测试通过；
294个浮点解析前缀与已有有限根样本尾和只作回归，不能当无限概率/内核证明。
精确Actions构建、公理、回归、覆盖及独立复核仍为接受门禁。移动配置、有符号差律、
素数传递及其余接收任务继续开放；本轮没有新增纸面来源或修改原始研究水位。

## 2026-09-30：REC 显式置信参数的实际矩阵恢复候选

在已验联合等待尾界/期望主线3b0d3aad上新增F3RecoveryConfidence.lean三条候选声明。
对原固定配置、0<δ<1及自然T满足T≥3^K log(choose(m,2)/δ)，将已验真实尾界反解为
实际失败概率≤δ，再通过已证明的矩阵恢复等价和可测补事件得到实际完整矩阵恢复
概率≥1−δ。K仍为真实有限根距最大值，不把成功事件定义为希望成立的概率结论。

源码111文件、740项目声明+1产生器覆盖与6项审计规则测试通过，但三条声明尚未编译。
36个数值阈值与既有有限根模型的精确有理成功概率仅作回归；精确Actions全部门禁和
独立数学复核仍待执行。此候选不涵盖移动配置、全素数传递、有符号差律或整个REC包；
原纸面来源及研究水位不变。

## 2026-09-30：REC-L12 单次截断证书真实 Haar 概率候选

新增F3TruncatedCertificateHaar.lean十二条候选声明，针对定理2.6式(2.13)：既有
不等或联合饱和证书的真实事件在L<H时等于原深度不等事件，在L≥H时等于共同H球。
因此复用已验单位Haar律给出3^(−L)或1/(2·3^(H−1))，并由实际事件包含得到统一下界。
原固定配置包装使用实际有限正根距，H截断的是R而非b+R；原始命中根的∞保留到截断。

候选尚未编译：源码112文件、752项目声明+1产生器覆盖及六项审计规则测试通过。
30个精确有限剩余类案例包含H=1、L=H和根命中，只是补充回归。H=0被公式明确排除；
该点实际成功率1而误用公式得1/2，体现正精度前提必要。有限批次截断矩阵失败界式(2.14)、
移动配置、素数传递和其他REC节点仍开放。11:09刷新172个实际远端分支，155原水位记录
仅master变化，原研究头未变；近期issues/PR仅本轮工程记录，没有新增外部证明包。
原始来源水位不更新；完整精确Actions门禁及独立复核仍待执行。

## 2026-09-30：REC-L12 实际有限批次截断矩阵概率候选

新增F3TruncatedBatchHaar.lean十一条候选声明，针对定理2.6式(2.14)。观测参数是
真实有限单位Haar乘积，单次同一参数作用于全部根。每对失败事件等于真实单次成功
补事件的时间乘积矩形；用已验统一成功率下界得到指数尾。已有截断矩阵算法失败
逐点等于规范i<j对失败的并集，系数恰为choose(m,2)，不假设根对独立。目标始终为
min(L,H)，对角线H，保留根命中原深度∞、联合饱和和空批次T=0。

候选尚未编译：源码113文件、763项目声明+1产生器覆盖及六项审计规则测试通过。
84个有限剩余类批次案例只作回归，包含真实矩阵、时间乘积、强相关根对和T=0；
不能代替精确Actions内核/公理/源码/覆盖门禁。移动配置、全素数采样与其他REC节点
仍开放；本轮沿用已接收纸面证明和既有来源水位。

## 2026-09-30：有限精度双输出完整分布不可辨识候选

新增F3TruncatedNonidentifiability.lean十四条候选声明。先由既有真实尾律、非负性和
根单点零测，使用锁定库的半直线测度唯一性识别完整原深度推前分布；显式证明标准
WithTop整数Borel可测性，保留根命中的∞，不利用非可测map默认分支。再通过可测min
截断和对角映射，证明两根距离均≥H时完整双输出分布相同；真实有限乘积推前接口
给出每个自然T（含0）的完整观测序列分布相同，不只是矩或个别概率相同。

原模型包装保留共同已知基础深度、各自正基深度、m=2、互异同模3单位根及H≥1；
显式比较真实距离H与更高K>H。只针对观测本身，不能解读为给出系数后也无法计算根距，
也不声称有限素数盒中的采样律完全相同。

候选尚未编译：源码114文件、777项目声明+1产生器覆盖及六项审计规则测试通过。
16个有限完整序列直方图案例及3个低于H的反向对照仅作回归。精确Actions全部门禁和
独立复核仍待执行；移动/素数采样、分歧律、被动下界、三等距根及其他任务继续开放。

## 2026-09-30 12:34 UTC：完整双输出截断观测分布已通过精确 CI

代码add478972bb5b3cd2a255cc0aab1ef6e078578b1，树7b38ee3b132fb3039518f4700ea3b4d509cdc44f，
[PR36715105909](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36715105909)
首轮完整成功；实际测试合并提交864ceb48a06109125d76756a0f41bd4161423530的文件树相同。
14条新增声明只有标准公理，778项总审计输出（777项目+1产生器）、114项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查均通过。

现已覆盖REC定理2.6的固定双根、有限精度完整观测分布不可辨识结论：标准单位Haar
采样下，两模型的真实根距均至少H时，每个有限T的完整双输出观测序列具有相同分布，
包括真实距离H与K>H的比较。原模型包装保留共同已知基深度、m=2、互异同模3单位根、
正基深和H≥1；根命中保留原深度∞，明确证明完整可测推前律，不使用非可测map默认值。

该结论仅针对观测接口，不是已知系数后的计算下界，也不是有限素数盒的分布相等。
16个完整序列直方图案例333768输入批次与3个反向控制仅为补充回归。独立数学/源码
复核通过；移动配置、素数传递、完整有符号分歧律、被动样本下界、三等距根停止律及
其他REC节点仍开放，整个包formalization_complete仍为false。此文档头不改已验Lean
代码、Audit或依赖，发布后仍需完整精确头CI和当前主分支检查。

## 2026-09-30：真实有符号深度原子律候选

新增F3SignedDepthLaw.lean十五条候选声明，针对REC-L3/定理2.1式(2.2)的
无条件有符号原子概率。事件显式要求两真实WithTop整数深度均为有限整数，
并在整数中相减；不把根命中的∞偷换为0。正差h≥1精确等于第一根L+h层，
负差对应第二根；零差精确等于既有等深事件。复用已验真实单位Haar层律与
零测根单点证明，得到±h质量3^(-(L+h))、零质量1−3^-L及几乎处处有定义。
原共享根模型包装保留单位/同模3/互异根与正基深前提。

本地源码115文件、792项目+1产生器Audit覆盖、六项审计规则测试通过，
尚无Lean构建或公理通过声明。12个有限剩余类案例只作回归，精度边界明确；
根命中代表仍排除为未定义，不用有限统计证明真正Haar零测。条件绝对值/符号
独立律仍为后续项，移动配置、素数传递、被动下界及三等距根任务亦保持开放。
外部查重和锁定API复用见f3_external_reuse.md本轮条目。

## 2026-09-30 13:06 UTC：真实有符号深度原子律通过精确 CI

代码744ec233e8ff7d4b55455743848db377cc353b1e，树030bf991d04063ae1405fc083706c635decc7984，
[push36718612456](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36718612456)与
[PR36718619580](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36718619580)
完整成功；实际测试合并ad9ed10c6a4485169ee1af58d4eefb6b84346044文件树相同。首轮仅有
零事件证明的集合成员展开和自然数转WithTop有限性两处编译问题，已用显式change及
锁定库WithTop.natCast_ne_top修正，十五条公开陈述和全部定义没有改变。

十五条新声明均仅标准公理；793项总输出（792项目+1产生器）、115项目源文件、650依赖
模块与版本锁、构建、内核回归、逐一覆盖及144240有限检查通过。独立数学源码复核
通过；12个剩余类案例9360代表元仍只是补充回归。

验收范围为REC-L3/式(2.2)的实际无条件有符号原子律：所有正h与负h的质量为
3^(-(L+h))，零质量1−3^-L，并证明有限整数原子几乎处处覆盖。实际根命中仍为∞且
不属于有限差原子，零测例外已单独证明；原共享根单位/同余/正基深前提保留。
条件绝对值分布、符号独立性、移动配置、素数转移、被动下界和三等距根等仍开放，
整个REC包formalization_complete=false。最终状态头只改文档，仍另行完整精确CI。

## 2026-09-30：实际条件化深度差原子律候选

新增F3ConditionalDepthLaw.lean十四条候选声明。直接使用锁定mathlib的
ProbabilityTheory.cond，将真实单位Haar限制并归一化到实际不等深事件；
由已验3^-L证明该事件质量非零，故确为概率测度。有限有符号原子仍几乎
处处覆盖，来自条件测度对原Haar的绝对连续性，不把根命中∞改成整数。
证明条件正/负h各为3^-h、零为0、绝对差h≥1为2·3^-h，并显式证明绝对
事件等价于两有限整数深度差的natAbs。原共享根模型包装保持全部域前提。

候选未编译：源码116文件、806项目+1产生器覆盖、六项审计规则通过。
12项实际有限剩余类条件化回归只辅助检查，保留根命中代表在条件事件内
而不归入有限差原子；不能代替Haar零测证明或Actions。完整符号/绝对值
独立性、移动配置、素数传递、被动下界及三等距根等仍开放。

## 2026-09-30 13:31 UTC：实际条件化正负与绝对差原子律通过精确 CI

代码84c62787c4758fd30d0e714b10bda278d29f4030，树ccef9dd53635e8d39acdad579e4193511baa57be，
[PR36721583571](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36721583571)
首轮完整成功。实际测试合并f821720e9bab520ef4a5186fcdd84609aa0221ac文件树相同。
十四条新声明均仅标准公理；807项总输出（806项目+1产生器）、116项目源码、650依赖
模块及固定版本、实际产生器与项目构建、内核回归、逐一覆盖和144240有限检查通过。

验收范围为真实不等深事件上的ProbabilityTheory.cond：正质量由已验3^-L推出，
条件测度确为概率测度；绝对连续性传递根例外零测和有限差几乎处处有定义。条件
正/负h≥1各为3^-h，零为0，绝对差h为2·3^-h；绝对事件已证明等价于真实有限整数
深度差的natAbs，而不是仅改名的离散分布。原配置包装保留实际单位根和共同模3
条件、正基深等原域。十二个有限条件化案例只是补充回归，独立数学源码复核通过。

完整符号与绝对值独立性仍未登记为完成；移动配置、素数转移、被动下界、三等距根
停止律及其他REC节点继续开放，formalization_complete=false。此最终文档头不改已验
数学源码/Audit/依赖，发布后仍需精确头完整CI和当前主分支检查。

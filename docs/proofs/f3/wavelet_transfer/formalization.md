# F3-WAV：形式化计划

来源数学状态：PAPER-AUDITED（`311b0a226c0a64854f495dd3d1561fefaf6cb6e6`）。
本次数学范围：第 1 节错误大小界的局部修正；其余证明沿用来源，未重新做全包审计。
Lean 状态：`F3-WAV-1-PROOF-BOUND` 的一般引理与四条回归已通过代码c7e5d7d的精确CI（仅此范围）；
完整 F3-WAV-1 条件传递与 F3-WAV-2–6 均未完成。

推荐模块：
- OmegaBalance/F3WaveletLocal.lean
- OmegaBalance/F3WaveletAP.lean
- OmegaBalance/F3WaveletSieve.lean

建议接口：
- f3Wavelet_block_cancel
- f3Wavelet_conditional_transfer
- f3Wavelet_twin_shift
- f3Wavelet_two_root_decomposition
- f3Wavelet_energy
- f3Wavelet_ap_bound
- f3Wavelet_divisor_transfer
- finite_padic_stationary_phase_indicator

优先形式化局部有限同余部分。单端素数渐近需要现成的等差数列素数分布接口；若仓库固定依赖中没有可复用接口，则保持外部阻塞状态，不人为新增数学假设。

注意：
1. 整除指标必须允许多项式值为零。
2. 有符号权使用整数/复数语义。
3. 双端素数联合计数目前只是精确接口，不是已证渐近。
4. 本次新增 1 条一般声明及 4 条回归声明，精确映射如下；其他计划接口仍未实现。


## 2026-09-30: F3-WAV-1-PROOF-BOUND

一般命题的全部公开前提为 `r : ℕ`, `h : ℤ`, `2 ≤ r`, `2 < h`,
`h < (3 : ℤ) ^ (2*r-1) - 2`。结论仅为
`¬ (3 : ℤ) ^ (2*r-1) ∣ h^2-4`。自然数指数中的减法保持原窗口定义，
`r ≥ 2` 显式保留；`h` 的乘法和减法全部在整数中。

| 纸面步骤/回归 | 精确 Lean 声明（均在 OmegaBalance） | 文件 |
|---|---|---|
| WAV-BOUND / 修正 proof §1 | `f3Wavelet_discriminant_not_dvd` | `OmegaBalance/F3WaveletLocal.lean` |
| r=2,h=10,H=10，96<27 为假 | `f3Wavelet_false_size_bound_example` | `OmegaBalance/F3DeeperExamples.lean` |
| 同一内点仍满足不整除结论 | `f3Wavelet_interior_nondivisibility_example` | 同上 |
| h=2 零判别式例外 | `f3Wavelet_zero_discriminant_example` | 同上 |
| 首个排除点 h=25，27 整除、81 不整除、权 -1 | `f3Wavelet_excluded_boundary_example` | 同上 |

主模块经根 `OmegaBalance.lean` 导入；四条回归进入既有 F3DeeperExamples 构建目标，
五条声明在 `scripts/Audit.lean` 一对一登记，不通过新基础函数包装空目标。
复用既有 mathlib 的 prime-power product 与整数正除数界 API；没有新的 gcd、赋值基础。

- [复用门](../../../f3_external_reuse.md#2026-09-30-f3-wav-1-proof-bound-target-first-reuse-gate)
- [精确来源与有限回归报告](../../../../reports/f3_wavelet_bound_correction.json)
- 工具链保持 Lean 4.34.0 / mathlib `5ed2965256430c3649e86755f9576b54eca72435`
- 本地只运行源码守卫、声明覆盖、有限整数验算及 diff 检查；没有 Lean/Lake 可执行文件
- 本次新声明未作本地 kernel、公理闭包或全库编译验证；只能在精确 head CI 全门禁后升级状态
- 上游目录只有四个 Markdown；没有 PDF/TeX 可导入，没有排版生成或渲染验证

### 原始来源保持不变

来源分支 `proof/f3-exploration-123-latest` 不被修改，仍引用固定提交
`311b0a226c0a64854f495dd3d1561fefaf6cb6e6` 的原四文件。
修正只在实现分支导入的副本中进行。原 proof blob 为
`f61e35e3ea3b80c58195422b520050e58470c0de`，错误位于原第 79–89 行。
正确分解论证已见主线研究来源 `82f93f9668a43aabd69258fe1682efa7804a03ec`
的 `docs/f3_balance_research/research_notes.md` §4（第 116–139 行）；
一般域来自原第二轮 `research_notes_round2.md` 第 44 行。

其余 WAV-L1–L13、实际权函数/条件传递、两根/小波、Fourier、AP、除数传递、
单端素数渐近与一般驻相仍开放；不从此引理推出双端素数估计或孪生素数无穷性。

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

# F3-WAV：形式化计划

数学状态：PAPER-AUDITED。Lean 状态：NOT-STARTED。

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
4. 新增 Lean 声明：0。

# F₃ 证明集

对整数 $n>1$，定义
\[
F_3(n)=v_3(n+1)-v_3(n-1).
\]
赋值在非零整数上按绝对值定义；$\Omega$ 按重数计。各文稿分别明确整数、三进、有限群及素数计数的定义域。

## 正文

| 文稿 | 内容 |
|---|---|
| [算术结构](arithmetic.md) | 符号、幂、相反层、间距分类、完全幂排除及 Liouville 计数恒等式 |
| [固定间距与联合深度律](F3_fixed_gaps.md) | 平方坐标、Haar 分布、多移位联合尾律与单素数输入计数 |
| [素数伸缩配置](prime_dilations.md) | 五素数伸缩族、任意精确升层与联合几何律 |
| [素数伸缩族的高阶乘积](prime_higher_products.md) | 任意高阶的低次数刚性、系数和判据、全素数深度律与同主系数对照族 |
| [共享步长的乘积联合深度](prime_product_correlations.md) | 多输出根距离、精确层闭式判据、三项不可实现证书与全素数联合律 |
| [深度矩与根距离恢复](prime_depth_moments.md) | 唯一分解深尾界、增强指数收敛、协方差恢复根树与有理联合生成函数 |
| [有限观测的根距离证书](prime_depth_reconstruction.md) | 不等深度证书、精确等待概率、被动采样下界与截断精度恢复 |
| [二次赋值差分权](quadratic_weights.md) | 有限驻相、判别式传递、两支差分、等差数列界与稀疏窗口 |
| [乘积核的谱](spectral_kernels.md) | 特征展开、投影恒等式、正负谱及短带匹配 |
| [平衡逆元几何](inverse_geometry.md) | 深度边界、全层二次正规形、斜线极限与精确盒计数 |
| [模双曲线筛](sieve_bounds.md) | 合并同余的矩形分布、Selberg 上界及三素数因子深度尾界 |
| [预筛层分布](presieved_geometry.md) | 逐线局部因子、增长预筛、面积主项及有界几乎素数下界 |
| [粗糙 Liouville 和](rough_liouville.md) | 精确 F₃ 层上的素数／半素数主项与增长模数负号定理 |

## 依赖与证明范围

正文按“定义—命题—证明”组织；外部定理在使用处列明前提并在文末给出来源。算术与有限计数的证明不以实验结果为依据。`presieved_geometry.md` 使用 `inverse_geometry.md` 的分支参数化及 `sieve_bounds.md` 的通用矩形计数。`prime_dilations.md`、`prime_higher_products.md` 与 `prime_product_correlations.md` 的素数主项使用已知的有限复杂度线性形式素数定理。

`prime_depth_moments.md` 在共享根模型上结合 Selberg 上界筛与素数唯一分解控制增长深度的尾部，推出增强的指数加权收敛、全部固定阶矩和有理联合生成函数。

`prime_depth_reconstruction.md` 使用固定共享根结构与固定精度素数分布，给出有限观测的无误判证书和采样复杂度；不依赖新的深尾估计。

这些文稿是数学书面证明，不等同于新增的 Lean 内核验证。机器证明接口见仓库中的 [OmegaBalance](../../OmegaBalance)；其核验要求以根目录 [AGENTS.md](../../AGENTS.md) 和正式验证流程为准。素数、几乎素数、预筛整数和均匀剩余类的结论各自保留完整假设，不相互替代。

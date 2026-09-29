# F3-MOM：共享素数步长的深度矩、根距离与生成函数

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-MOM-1\`、\`F3-MOM-2\`、\`F3-MOM-3\`、\`F3-MOM-4\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源 | [prime_depth_moments.md](../../../f3_balance_research/prime_depth_moments.md) |
| Lean 状态 | 尚未形式化 |
| 外部输入 | 固定形状素数主项与固定精度分布；Selberg 上界筛；标准乘法函数估计 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## F3-MOM-1：统一尾界与极深尾改进

沿用固定共享根素数族，记
\[
D_i=b+R_i,\qquad Z=\max_iR_i.
\]

中等深度满足
\[
\Pr_X(Z\ge t)\ll 3^{-t}+X^{-3/4}
\]
只要 \(3^{b+t}\le X^{1/2}\)。

所有深度满足
\[
\Pr_X(Z\ge t)\ll(\log X)^a(3^{-t}+X^{-1}).
\]

进一步，对任一固定输出 \(P_i\)，映射
\[
(n,d)\mapsto P_i(n,d)
\]
在全素数参数集上单射。因此
\[
\boxed{
\Pr_X(Z\ge t)
\ll
(\log X)^a
\min\{3^{-t}+X^{-1},\,X^{q-2}3^{-t}\}.
}
\]

这里单射性来自：乘积的 \(q\) 个素数因子严格递增，唯一分解恢复每个线性因子，再由前两个因子恢复 \(n,d\)。

## F3-MOM-2：指数加权分布与全部固定阶矩

对每个固定
\[
0<\eta<\frac1{q-1},
\]
有
\[
\boxed{
\sum_{\mathbf r}
3^{\eta\max_i r_i}
|\mu_X(\mathbf r)-\mu(\mathbf r)|
\to0.
}
\]

因此任意固定多元多项式矩收敛；更一般地，只要
\[
|F(\mathbf r)|\le C_F3^{\eta\max r_i},
\qquad \eta<1/(q-1),
\]
都有
\[
\mathbb E_XF(\mathbf R)\to\mathbb E_\mu F(\mathbf R).
\]

相比前版 \(\eta<1/q\)，本版利用 F3-MOM-1 的极深尾单射界提升到
\[
\boxed{\eta<1/(q-1)}.
\]

## F3-MOM-3：协方差恢复根距离

对每个输出：
\[
\lim_X\mathbb E_XD_i=b+\frac34,
\qquad
\lim_X\operatorname{Var}_X(D_i)=\frac{15}{16}.
\]

对 \(i\ne j\)，若
\[
L_{ij}=v_3(\alpha_i-\alpha_j),
\]
则
\[
\boxed{
\lim_X\mathbb E_X(D_i-D_j)^2=3^{1-L_{ij}},
}
\]
\[
\boxed{
\lim_X\operatorname{Cov}_X(D_i,D_j)
=
\frac{15}{16}-\frac32\,3^{-L_{ij}},
}
\]
\[
\boxed{
\lim_X\operatorname{Corr}_X(D_i,D_j)
=
1-\frac85\,3^{-L_{ij}}.
}
\]

所以带标签协方差矩阵唯一恢复全部 \(L_{ij}\)，从而在已知共享根模型内恢复根树和完整联合深度律。

## F3-MOM-4：多元有理概率生成函数

令
\[
K=\max_{i\ne j}L_{ij}.
\]
超过 \(K\) 后，最多只有一个坐标继续增长；若 \(R_i=u>K\)，则
\[
R_j=L_{ij}\qquad(j\ne i),
\]
且该向量概率为 \(3^{-u}\)。

因此局部概率生成函数
\[
\Phi(\mathbf z)=\mathbb E_\mu\prod_i z_i^{R_i}
\]
在 \(|z_i|<3\) 内有显式有理形式：
\[
\boxed{
\Phi(\mathbf z)
=
A_K(\mathbf z)
+
\sum_i
\left(\prod_{j\ne i}z_j^{L_{ij}}\right)
\frac{(z_i/3)^{K+1}}{1-z_i/3}.
}
\]

其中有限部分 \(A_K\) 也可直接由根簇树写成至多 \(1+mK\) 项的有限和。

令
\[
S_0=\sum_iR_i,\qquad
s_i=\sum_{j\ne i}L_{ij}.
\]
则对所有
\[
r>mK
\]
有精确局部尾：
\[
\boxed{
\mu(S_0=r)=3^{-r}\sum_i3^{s_i}.
}
\]

全素数生成函数
\[
\Phi_X(\mathbf z)=\mathbb E_X\prod_i z_i^{R_i}
\]
在
\[
\boxed{|z_i|<3^{1/(q-1)}}
\]
的任意紧多圆盘上一致收敛到 \(\Phi\)，任意固定阶复偏导也一致收敛。

## 边界

- 形状固定后再令 \(X\to\infty\)。
- 局部生成函数半径 \(|z_i|<3\) 大于当前已证明的全素数收敛半径，二者不可混同。
- 不给出 Green–Tao–Ziegler 主项的有效误差。
- 不给出深度随 \(X\) 增长时的统一相对素数主项。

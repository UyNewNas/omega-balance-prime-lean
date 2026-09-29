# F3-MOM：共享素数步长的深度矩与根距离恢复

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-MOM-1\`、\`F3-MOM-2\`、\`F3-MOM-3\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源研究稿 | [prime_depth_moments.md](../../../f3_balance_research/prime_depth_moments.md) |
| Lean 状态 | 尚未形式化 |
| 外部依赖 | 固定形状素数主项与固定精度联合分布；Selberg 上界筛；标准乘法函数求和 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 固定共享根素数族

固定 \(k,s\ge1\)，令
\[
q=3^s,\qquad b=k+s,\qquad M=3^b.
\]
采用研究稿中的固定形状 \(\mathcal H\)、固定 \(W\)、输出乘积 \(P_i\)、深度
\[
D_i=F_3(P_i),\qquad R_i=D_i-b.
\]

假设此前共享根结果已经给出：

1. 对每个允许的 \(n\)，
   \[
   R_i=v_3(d-\alpha_i(n));
   \]
2. 根距离
   \[
   L_{ij}=v_3(\alpha_i-\alpha_j)
   =
   b+v_3(E_i-E_j)
   \]
   有限且与 \(n\) 无关；
3. 全素数参数集合 \(\mathcal P(X)\) 满足
   \[
   B(X)=|\mathcal P(X)|
   =
   (\kappa+o(1))
   \frac{X^2}{(\log X)^a},
   \qquad \kappa>0;
   \]
4. 每个固定有限深度向量的点概率收敛到单位步长 Haar 根模型 \(\mu\)。

本包新增的内容是从固定精度分布推进到**一致尾控制、加权分布收敛和无界矩收敛**。

## 2. 定理 F3-MOM-1：全素数族的一致深度尾界

令
\[
Z=\max_i R_i.
\]
存在依赖固定形状的常数 \(C,X_0\)，使对所有 \(X\ge X_0\)：

若
\[
t\ge1,\qquad3^{b+t}\le X^{1/2},
\]
则
\[
\boxed{
\Pr_X(Z\ge t)
\le
C\left(3^{-t}+X^{-3/4}\right).
}
\]

对所有 \(t\ge1\)，
\[
\boxed{
\Pr_X(Z\ge t)
\le
C(\log X)^a
\left(3^{-t}+X^{-1}\right).
}
\]

并且每个被计数参数点满足
\[
\boxed{
0\le Z\le q\log_3X+C.
}
\]

证明使用：

- 精确的增长模数剩余类计数；
- 与素数条件联合的二维格点计数；
- Selberg 上界筛；
- 对大深度直接丢弃素性后的整数点计数。

## 3. 定理 F3-MOM-2：指数加权总变差与全部固定阶矩

对每个固定
\[
0<\eta<1/q,
\]
有
\[
\boxed{
\sum_{\mathbf r\in\mathbb Z_{\ge0}^{m}}
3^{\eta\max_i r_i}
|\mu_X(\mathbf r)-\mu(\mathbf r)|
\longrightarrow0.
}
\]

因此任意固定多元多项式 \(F\) 满足
\[
\boxed{
\mathbb E_XF(R_1,\ldots,R_m)
\longrightarrow
\int F(\mathbf r)\,d\mu(\mathbf r).
}
\]

更一般地，只要
\[
|F(\mathbf r)|
\le
C_F3^{\eta\max_i r_i},
\qquad \eta<1/q,
\]
同样成立。

这里的指数范围来自当前粗尾界，不声明最优。

## 4. 定理 F3-MOM-3：协方差精确恢复根距离

对每个 \(i\)，
\[
\boxed{
\lim_X\mathbb E_XD_i=b+\frac34,
\qquad
\lim_X\operatorname{Var}_X(D_i)=\frac{15}{16}.
}
\]

对 \(i\ne j\)，
\[
\boxed{
\lim_X\mathbb E_X(D_i-D_j)^2
=
3^{1-L_{ij}},
}
\]
\[
\boxed{
\lim_X\operatorname{Cov}_X(D_i,D_j)
=
\frac{15}{16}-\frac32\,3^{-L_{ij}},
}
\]
以及
\[
\boxed{
\lim_X\operatorname{Corr}_X(D_i,D_j)
=
1-\frac85\,3^{-L_{ij}}.
}
\]

因此
\[
\boxed{
3^{-L_{ij}}
=
\frac23
\left(
\frac{15}{16}-\Sigma_{ij}
\right)
=
\frac13
\lim_X\mathbb E_X(D_i-D_j)^2,
}
\]
其中
\[
\Sigma_{ij}
=
\lim_X\operatorname{Cov}_X(D_i,D_j).
\]

所以在这个固定共享根模型中，**带标签的极限协方差矩阵确定全部根距离 \(L_{ij}\)**，继而确定根树、整个局部联合深度律与精确模式可实现性。

它恢复的是根间距离，不是根的绝对位置。

## 5. 边界

- 固定形状参数必须先于 \(X\to\infty\) 固定。
- 不提供 Green–Tao–Ziegler 主项的有效误差。
- 不保证随 \(X\) 增长的深层事件具有相对主项或非空。
- 不推出固定素数步长或固定孪生间距。
- 点概率或普通总变差收敛本身不足以推出无界矩；本包的新增核心正是一致可积性。

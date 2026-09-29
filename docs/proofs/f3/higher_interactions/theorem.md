# F3-HI：固定伸缩素数族中的高阶相互作用

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-HI-1\`、\`F3-HI-2\`、\`F3-HI-3\` |
| 状态 | \`PAPER-AUDITED\` |
| 内容类型 | 完整书面证明；固定形状计数定理 + 二阶信息不完备 + 有限模式实现 |
| 整理日期 | 2026-09-29 |
| Lean 状态 | 尚未形式化；不属于 \`LEAN-PROVED\` |
| 外部依赖 | Green–Tao 的复杂度至多 2 素数线性形式定理；一般有限模式实现使用后续 Green–Tao–Ziegler 有限复杂度版本 |

[PDF 版](paper.pdf) · [完整证明](proof.md) · [引理 DAG 与审计记录](scaffolding.md) · [形式化计划](formalization.md)

本包从研究稿 \`docs/f3_balance_research/prime_higher_products.md\` 中抽取并固定最终定理。研究稿保留探索背景；本目录保存稳定定理、完整证明、审计脚手架、形式化计划和 PDF 排版版本。

## 1. 定义

对整数 \(m>1\)，定义
\[
F_3(m)=v_3(m+1)-v_3(m-1)\in\mathbb Z.
\]

固定整数 \(k\ge1\)，令
\[
M=3^{k+1},\qquad
p_0=n,\quad p_1=n+2Md,\quad p_2=n+6Md.
\]
并记
\[
D(n,d)=F_3(p_0p_1p_2).
\]

对 \(X>0\)，定义
\[
\mathcal Q_k(X)=
\{(n,d):X<n,d\le2X,\ d,p_0,p_1,p_2\text{ 全为素数},\ F_3(n)=k\}.
\]

再令
\[
\mathfrak C=
\prod_{\substack{\ell\ge5\\ \ell\text{ prime}}}
\frac{\ell^2(\ell-3)}{(\ell-1)^3},
\qquad
\kappa_k=3^{2-k}\mathfrak C.
\]
该无穷乘积严格为正。

## 2. 定理 F3-HI-1：固定形状的完整深度分布

在 \(\mathcal Q_k(X)\) 中恒有
\[
\boxed{
F_3(p_0)=F_3(p_1)=F_3(p_2)=k,
}
\]
以及
\[
\boxed{
F_3(p_0p_1)=F_3(p_0p_2)=F_3(p_1p_2)=-k.
}
\]

并且
\[
\boxed{
|\mathcal Q_k(X)|
=
(\kappa_k+o_k(1))
\frac{X^2}{(\log X)^4}.
}
\]

对每个固定整数 \(R\ge k+1\)，
\[
\boxed{
\#\{(n,d)\in\mathcal Q_k(X):D(n,d)=R\}
=
(\kappa_k w_k(R)+o_{k,R}(1))
\frac{X^2}{(\log X)^4},
}
\]
其中
\[
w_k(R)=
\begin{cases}
\dfrac12,&R=k+1,\\[2mm]
3^{-(R-k-1)},&R\ge k+2.
\end{cases}
\]

因此每个允许深度 \(R\ge k+1\) 都有无穷多个全素数实现，而且偏移系数 \(2M,6M\) 不依赖于 \(R\)。

特别地，\(k=1\) 时固定形状为
\[
(n,n+18d,n+54d),
\]
对每个预先指定的 \(R\ge2\) 都存在无穷多个素数 \(d,n,n+18d,n+54d\)，满足三个单点值全为 \(1\)、三个两两乘积值全为 \(-1\)，而三因子乘积值恰为 \(R\)。

## 3. 推论 F3-HI-2：全部二阶数据仍不能决定三阶输出

即使同时知道：

1. 三个输入都来自同一固定伸缩形状；
2. 步长 \(d\) 本身为素数；
3. 三个单点 \(F_3\) 值；
4. 三个两两乘积 \(F_3\) 值；

三因子乘积的 \(F_3\) 仍没有由这些信息给出的有限上界。事实上，对固定 \(k\)，同一组六个低阶数据对应每个 \(R\ge k+1\) 的无穷多个全素数实现。

## 4. 定理 F3-HI-3：有限剩余模式的素数伸缩实现

固定 \(s\ge2\)、\(A\ge1\)，令 \(Q=3^A\)。给定模 \(Q\) 的单位剩余类
\[
a_0,\ldots,a_{s-1},b\in(\mathbb Z/Q\mathbb Z)^\times.
\]
则存在固定整数
\[
0=h_0<h_1<\cdots<h_{s-1}
\]
和常数 \(c>0\)，使满足
\[
(n,d)\equiv(a_0,b)\pmod Q,\qquad X<n,d\le2X,
\]
以及
\[
d,\ n+h_0d,\ldots,n+h_{s-1}d
\]
全部为素数的参数对数满足
\[
\boxed{
(c+o(1))\frac{X^2}{(\log X)^{s+1}}.
}
\]
并且每个端点满足
\[
n+h_i d\equiv a_i\pmod Q.
\]

### 有限 \(F_3\) 单项式模式推论

设有限多个非空单项式
\[
Y_\alpha(x)=\prod_i x_i^{e_{\alpha,i}}
\]
及目标非零整数 \(f_\alpha\) 已由某组正整数 \(x_i\) 实现：
\[
3\nmid x_i,\qquad F_3(Y_\alpha(x))=f_\alpha.
\]
取
\[
A>\max_\alpha |f_\alpha|
\]
并令 \(a_i\equiv x_i\pmod{3^A}\)。则存在某个固定伸缩形状 \(p_i=n+h_i d\)，使上述全部单项式 \(F_3\) 等式由无穷多组素数端点同时实现，且 \(d\) 也为素数。

这里形状允许依赖整组目标数据；F3-HI-1 的特殊性在于其偏移形状不随三因子目标深度 \(R\) 改变。

## 5. 边界与不声称事项

- 本结果的实际间距为 \(2Md,6Md\)，其中 \(d\) 可变；不推出固定间距孪生素数或 Dickson 型固定步长无穷性。
- 第 2–3 节的无穷性使用已发表的素数线性形式定理；本仓库没有重新证明该深层外部输入。
- 有限实验只用于排错和展示，不承担无限命题的证明责任。
- 本结果尚未进入 Lean；\`PAPER-AUDITED\` 不等于 \`LEAN-PROVED\`。
- PDF 是稳定书面证明的排版层，不额外提升证明状态。
- 本包不声称这些现象在文献中首次出现；首创性查新是独立任务。

## 6. 外部文献

[GT10] Ben Green and Terence Tao, *Linear equations in primes*, Annals of Mathematics **171** (2010), 1753–1850. DOI: \`10.4007/annals.2010.171.1753\`.

- 复杂度至多 2 的情形在该文中无条件成立。
- 出版页：https://annals.math.princeton.edu/2010/171-3/p08

一般有限复杂度实现还使用 Green–Tao 后续的 Möbius–nilsequence 结果与 Green–Tao–Ziegler 的逆定理，从而使有限复杂度线性形式素数渐近无条件成立。

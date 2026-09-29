# F3-PAT-1：书面证明

状态：`PAPER-PROVED`。精确陈述见 [theorem.md](theorem.md)。下文先固定七个赋值，再利用一个已发表的无条件定理保证四个线性形式同时为素数。

## 1. 精确赋值的同余稳定性

**引理 1.** 设 $A,B$ 为正整数，$R\ge1$，且

$$
A\equiv B\pmod{3^R},\qquad v_3(B)=e<R.
$$

则 $v_3(A)=e$。

**证明。** 写 $B=3^eb$，其中 $3\nmid b$。存在整数 $z$ 使

$$
A=3^e\bigl(b+3^{R-e}z\bigr).
$$

因 $R-e\ge1$，括号模 $3$ 同余于 $b$，不被 $3$ 整除。证毕。

## 2. 一个同余类固定全部七个值

令 $Q=729=3^6$。假设 $n\ge2$、$d\ge1$，并且

$$
n\equiv5\pmod Q,\qquad d\equiv1\pmod Q.
$$

令 $(h_0,h_1,h_2,h_3)=(0,38,92,146)$、$p_i=n+h_id$，则

$$
(p_0,p_1,p_2,p_3)\equiv(5,43,97,151)\pmod Q.
$$

四个代表元两侧的赋值如下：

| $b$ | $v_3(b+1)$ | $v_3(b-1)$ | 差 |
|---:|---:|---:|---:|
| 5 | 1 | 0 | 1 |
| 43 | 0 | 1 | −1 |
| 97 | 0 | 1 | −1 |
| 151 | 0 | 1 | −1 |

这些赋值都小于 6。对每个 $p_i\pm1$ 使用引理 1，即得四个指定单点值。

乘积加一满足

$$
\begin{aligned}
p_0p_1+1&\equiv216=3^3\cdot8\pmod Q,\\
p_0p_2+1&\equiv486=3^5\cdot2\pmod Q,\\
p_0p_3+1&\equiv756=3^3\cdot28\pmod Q.
\end{aligned}
$$

三个赋值 $3,5,3$ 均小于 6，所以引理 1 给出精确值，而非仅给下界。又因 $p_0\equiv2$、$p_i\equiv1\pmod3$，有 $p_0p_i-1\equiv1\pmod3$，其赋值为零。故全部七个 $F_3$ 值成立。

这一段完全不需要素数性。

## 3. 将全素数要求写成四个线性形式

作代换

$$
n=5+Qu,\qquad d=1+Qv.
$$

定义 $L_i(u,v)=5+h_i+Qu+Qh_iv$，即

$$
\begin{aligned}
L_0(u,v)&=5+729u,\\
L_1(u,v)&=43+729u+27702v,\\
L_2(u,v)&=97+729u+67068v,\\
L_3(u,v)&=151+729u+106434v.
\end{aligned}
$$

下面在整数方框 $K_X=[X,2X]^2$ 中计数，$X$ 为趋于无穷的正整数。所有系数和常数项固定；四个值在该方框中均为正，且统一满足

$$
729X\le L_i(u,v)\le215000X\qquad(X\ge1).
$$

故所有对数权都与 $\log X$ 渐近等价。原定理的尺度可取 $N=2X$；$K_X\subset[-N,N]^2$、面积为 $X^2$，形式的尺寸有与 $X$ 无关的上界。

## 4. 复杂度至多 2

线性部分的系数向量为 $Q(1,h_i)$。若 $i\ne j$，则

$$
\det\begin{pmatrix}Q&Qh_i\\Q&Qh_j\end{pmatrix}
=Q^2(h_j-h_i)\ne0.
$$

因此不同的 $L_i,L_j$ 不满足任何仿射依赖 $L_i=aL_j+b$（$a,b\in\mathbb Q$）。对每个 $i$，把另外三个形式分别置于三个单元素组；$L_i$ 不在任一组的仿射线性张成中。按照 [GT10, Definition 1.5]，系统复杂度至多 $3-1=2$。

## 5. 所有局部因子为正，且乘积收敛为正数

对素数 $\ell$，记

$$
\beta_\ell=\frac1{\ell^2}
\sum_{u,v\bmod\ell}
\prod_{i=0}^3\left(\frac{\ell}{\ell-1}\,
\mathbf1_{\ell\nmid L_i(u,v)}\right).
$$

当 $\ell=3$ 时，四个形式恒为 $(2,1,1,1)\pmod3$，故

$$
\beta_3=(3/2)^4>0.
$$

当 $\ell\ne3$ 时，$Q$ 在模 $\ell$ 下可逆。取

$$
u\equiv-4Q^{-1}\pmod\ell,\qquad
v\equiv-Q^{-1}\pmod\ell,
$$

便有 $n\equiv1,d\equiv0\pmod\ell$，所以全部 $L_i\equiv1\pmod\ell$。由此 $\beta_\ell>0$。

还须证明无穷乘积不因尾部而归零。对 $\ell>146$，四个 $h_i$ 模 $\ell$ 互异，且 $(u,v)\mapsto(n,d)$ 是模 $\ell$ 的双射。当 $d=0$ 时有 $\ell-1$ 个允许的 $n$；当 $d\ne0$ 时有 $\ell-4$ 个允许的 $n$。故

$$
\beta_\ell
=\frac{(\ell-1)(\ell-3)}{\ell^2}
\left(\frac\ell{\ell-1}\right)^4
=\frac{\ell^2(\ell-3)}{(\ell-1)^3}
=1-\frac{3\ell-1}{(\ell-1)^3}.
$$

因此 $\sum_{\ell>146}|\beta_\ell-1|<\infty$，尾部乘积收敛且非零；有限个小素数的因子也都为正。于是

$$
\mathfrak S_L:=\prod_{\ell\text{ prime}}\beta_\ell\in(0,\infty).
$$

这里没有用“每个因子正”替代“整个乘积正”的论证。

## 6. 唯一的全局外部输入

使用 [GT10, Corollary 1.7]：复杂度至多 2 的仿射线性形式满足该文的素数计数渐近 (1.8)。对这里固定的四形式、二维正值方框，它给出

$$
\#\{(u,v)\in K_X\cap\mathbb Z^2:
L_0(u,v),L_1(u,v),L_2(u,v),L_3(u,v)\text{ 均为素数}\}
=(\mathfrak S_L+o(1))\frac{X^2}{(\log X)^4}.
$$

这里的引用是无条件推论，不是把原文的一般条件性 Main Theorem 直接当成无条件定理。式 (1.8) 数的是素数，不是素数幂；它的归约说明见原文第 5–6 页。第 3–5 节已经逐项核对本应用的尺寸、区域、复杂度与局部条件。

由于 $\mathfrak S_L>0$，右边趋于无穷。

## 7. 完成构造并固定量词

对上述每个全素数参数对，取 $n=5+729u,d=1+729v$。该映射为单射；第 2 节保证七个 $F_3$ 值。并且在 $K_X$ 上 $n,d$ 同时趋于无穷，所以对任意 $B\ge1$，选择足够大的 $X$ 就得到 $n>B,d>B$。

这证明 F3-PAT-1 以及指定模 729 剩余类的加强版。证毕。

固定 $d$ 会把四个形式变成单变量且线性部分互相成比例；本证明不能在固定 $d$ 的切片上使用。以上 $\mathfrak S_L$ 和计数方框只对应所选充分同余类，不是所有七值模式的总比例。

## 参考文献

[GT10] Ben Green and Terence Tao, *Linear equations in primes*, Annals of Mathematics **171** (2010), 1753–1850，DOI `10.4007/annals.2010.171.1753`。[出版页](https://annals.math.princeton.edu/2010/171-3/p08)；[固定核对版本](https://arxiv.org/pdf/math/0606088v2)。定位：Definition 1.5（PDF 第 7 页）、Corollary 1.7（第 10 页）、计数式 (1.8) 与说明（第 5–6 页）。

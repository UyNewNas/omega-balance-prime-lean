# 素数伸缩族中二阶数据不变的三因子深度律

对整数 $u>1$，定义
\[
F_3(u)=v_3(u+1)-v_3(u-1).
\]
赋值只作用于非零整数。所有计数定理先固定整数参数，再令 $X\to\infty$。本文使用已知的有限复杂度线性形式素数定理；并不证明该外部定理。

## 1. 固定形状与主定理

固定 $k\ge1$，令
\[
M=3^{k+1},\qquad p_0=n,\quad p_1=n+2Md,\quad p_2=n+6Md.
\]
定义
\[
\mathcal Q_k(X)=\{(n,d)\in\mathbb Z^2:X<n,d\le2X,\ d,p_0,p_1,p_2\text{ 均为素数},\ F_3(n)=k\}.
\]
记 $B_k(X)=|\mathcal Q_k(X)|$，$D(n,d)=F_3(p_0p_1p_2)$，以及
\[
\mathfrak C=\prod_{\ell\ge5,\ \ell\text{ 为素数}}\frac{\ell^2(\ell-3)}{(\ell-1)^3},
\qquad \kappa_k=3^{2-k}\mathfrak C.
\]
每个乘积因子为正，且等于 $1-(3\ell-1)/(\ell-1)^3=1+O(\ell^{-2})$，所以 $\mathfrak C>0$。

### 定理 1.1

在 $\mathcal Q_k(X)$ 中，恒有
\[
F_3(p_0)=F_3(p_1)=F_3(p_2)=k,
\qquad F_3(p_0p_1)=F_3(p_0p_2)=F_3(p_1p_2)=-k.
\tag{1.1}
\]
并且
\[
B_k(X)=(\kappa_k+o_k(1))\frac{X^2}{(\log X)^4}.
\tag{1.2}
\]
对每个固定整数 $R\ge k+1$，
\[
\#\{(n,d)\in\mathcal Q_k(X):D(n,d)=R\}
=\left(\kappa_k\,w_k(R)+o_{k,R}(1)\right)\frac{X^2}{(\log X)^4},
\tag{1.3}
\]
其中
\[
w_k(R)=\begin{cases}
1/2,&R=k+1,\\
3^{-(R-k-1)},&R\ge k+2.
\end{cases}
\]

因此，对每个预先指定的 $R\ge k+1$，存在无穷多个参数对使四个数 $d,p_0,p_1,p_2$ 均为素数，同时满足 (1.1) 和 $D=R$。偏移系数 $2M,6M$ 不依赖于 $R$。

## 2. 确定性约化

### 引理 2.1

设 $n>1,d>0$、$3\nmid d$，且 $F_3(n)=k$。则 (1.1) 成立，并有 $D(n,d)\ge k+1$。

**证明。** 写
\[
n=-1+3^k a,\qquad3\nmid a.
\]
三个 $p_i$ 均同余于 $n\pmod{3^{k+1}}$，故其单点 $F_3$ 均为 $k$。对任意 $i\ne j$，
\[
p_ip_j-1\equiv n^2-1\equiv-2\cdot3^ka\pmod{3^{k+1}},
\]
且 $p_ip_j\equiv1\pmod3$。所以两因子乘积的 $F_3$ 都为 $-k$。

直接展开
\[
(n+1)^3-3(n+1)^2+3(n+1)=n^3+1
\]
给出
\[
A(n):=\frac{n^3+1}{M}
=a-3^ka^2+3^{2k-1}a^3\in\mathbb Z,
\qquad A(n)\equiv a\pmod3.
\]
三个因子的乘积满足
\[
p_0p_1p_2+1=M G_n(d),
\qquad G_n(d)=A(n)+8n^2d+12Mn d^2.
\tag{2.1}
\]
因为乘积模 $3$ 为 $-1$，故
\[
D(n,d)=k+1+v_3(G_n(d)).
\tag{2.2}
\]
正整数输入使 $G_n(d)>0$，这里没有零自变量。$\square$

### 引理 2.2（简单根与精确有限计数）

固定上述 $n$，令 $T\ge1$。对模 $3^T$ 的单位 $d$ 均匀计数，则
\[
\Pr(G_n(d)\not\equiv0\pmod3)=1/2,
\]
且对 $1\le t\le T$，
\[
\Pr(3^t\mid G_n(d))=\frac1{2\cdot3^{t-1}}.
\tag{2.3}
\]
这里概率只是有限剩余类的比例。对 $1\le t<T$，精确赋值为 $t$ 的比例为 $3^{-t}$；截断顶层只表达赋值至少为 $T$。

**证明。** 模 $3$ 下有
\[
G_n(d)\equiv a+2d,\qquad G_n'(d)=8n^2+24Mn d\equiv2.
\]
所以模 $3$ 的唯一根是 $d\equiv a$，是单位。若 $u$ 为模 $3^t$ 的根，则
\[
G_n(u+3^t b)\equiv G_n(u)+3^t bG_n'(u)\pmod{3^{t+1}}.
\]
因为导数为单位，$b\bmod3$ 中恰有一个选择继续为根。归纳得模 $3^t$ 恰有一个根，且始终为单位。因此模 $3^T$ 的 $2\cdot3^{T-1}$ 个单位中，恰有 $3^{T-t}$ 个满足门槛。这给出 (2.3)，相邻门槛相减即得精确赋值比例。$\square$

### 推论 2.3

在任意足够高精度的有限参数类中，条件化于 $F_3(n)=k$、$3\nmid d$ 后，$D=k+1$ 的比例为 $1/2$；$D=R\ge k+2$ 的比例为 $3^{-(R-k-1)}$。

**证明。** 固定每一个 $n$ 类后，引理 2.2 给出的比例都相同，因此对 $n$ 类求和仍成立。具体地，判定 $D=R$ 可取参数模数 $3^A$，其中 $A\ge R+1$。所有多项式值模 $3^{R+1}$ 均由此决定；取整商 $G_n$ 的所需精度亦由 (2.1) 保证。$\square$

## 3. 从有限参数类到四个素数

采用 [1–3] 的以下已知结论：固定的非恒定整数仿射线性形式，若线性部分两两不成比例，则在所有形式均为正且与 $X$ 同阶的凸盒中，同时取素数的计数为
\[
\left(\prod_\ell\beta_\ell+o(1)\right)
\frac{\operatorname{area}(K_X)}{(\log X)^s},
\quad
\beta_\ell=\ell^{-2}\sum_{x,y\bmod\ell}\prod_{i=1}^s
\frac{\ell}{\ell-1}\mathbf1_{\ell\nmid\psi_i(x,y)}.
\tag{LF}
\]
这里 $s$ 是线性形式数。四个两两不成比例的形式具有复杂度至多 $2$，本节已由 [1, Corollary 1.7] 的无条件范围覆盖。一般有限复杂度形式的版本还使用 [2–3]。从 von Mangoldt 加权形式到上述素数指示计数，可排除高次素数幂：固定一个非恒定形式取高次素数幂的参数点数为 $O(X^{3/2}\log X)$，其加权贡献为 $o(X^2)$；其余各对数权均为 $\log X+O(1)$。

### 引理 3.1

固定 $A\ge k+1$、$Q=3^A$，取模 $Q$ 的参数类 $(n,d)\equiv(b,c)$，其中 $F_3(n)=k$ 在该类上成立，且 $3\nmid c$。则该类内四个数同时为素数的计数为
\[
\left(\frac{\mathfrak S}{Q^2}+o_{k,Q}(1)\right)\frac{X^2}{(\log X)^4},
\qquad\mathfrak S=\frac{81}{4}\mathfrak C.
\tag{3.1}
\]
主系数不依赖允许类的具体代表。

**证明。** 代入 $n=b+Qx,d=c+Qy$。四个线性部分的方向为
\[
(0,1),\ (1,0),\ (1,2M),\ (1,6M),
\]
两两不成比例。模 $3$ 下四个形式全部为单位，所以局部因子为 $(3/2)^4$。

对 $\ell\ne3$，参数变换在模 $\ell$ 可逆。要求 $d\ne0$ 后，$n/d$ 必须避开 $0,-2M,-6M$。在 $\ell=2$ 时三类重合，合格参数只有 $(n,d)=(1,1)$，局部因子为 $4$。对 $\ell\ge5$，三个类互异，因为非零差为 $2M,4M,6M$，没有素因子大于 $3$；合格参数数为 $(\ell-1)(\ell-3)$，局部因子为 $\ell^2(\ell-3)/(\ell-1)^3$。

所有局部因子均为正且其乘积收敛，故乘积为 $(3/2)^4\cdot4\mathfrak C=81\mathfrak C/4$。参数盒面积为 $X^2/Q^2$。应用 (LF)。$\square$

**定理 1.1 的证明。** 模 $Q=3^A$ 下满足基础条件的参数类总数为
\[
\bigl(2\cdot3^{A-k-1}\bigr)\bigl(2\cdot3^{A-1}\bigr)
=4\cdot3^{2A-k-2}.
\]
将 (3.1) 对这些固定且有限的类求和，系数为
\[
\frac4{3^{k+2}}\frac{81}{4}\mathfrak C=3^{2-k}\mathfrak C=\kappa_k.
\]
得到 (1.2)。对精确值 $R$ 取 $A\ge R+1$，由推论 2.3，事件类恰占比例 $w_k(R)$，每类的素数主系数仍相同，故得到 (1.3)。确定性部分由引理 2.1 给出。各 $w_k(R)$ 严格为正，计数趋于无穷，即得存在性结论。$\square$

### 推论 3.2（二阶数据不决定三因子输出）

即使输入限定为同一固定形状
\[
(n,n+2\cdot3^{k+1}d,n+6\cdot3^{k+1}d)
\]
中的素数，且 $d$ 也为素数，三个单点 $F_3$ 值和三个两因子乘积 $F_3$ 值仍不能确定三因子乘积的 $F_3$ 值。事实上，同一组二阶数据 (1.1) 对应每个整数 $R\ge k+1$ 的无穷多个实现。

**证明。** 对每个 $R$ 使用定理 1.1；形状只依赖 $k$。$\square$

## 4. 任意有限局部乘积模式的伸缩实现

### 定理 4.1（有限剩余类的素数实现）

给定整数 $s\ge2$、$A\ge1$，令 $Q=3^A$。任取模 $Q$ 的单位 $a_0,\ldots,a_{s-1}$ 和 $b$。存在固定整数
\[
0=h_0<h_1<\cdots<h_{s-1},
\]
使满足
\[
(n,d)\equiv(a_0,b)\pmod Q,\quad X<n,d\le2X,
\]
\[
d,n+h_0d,\ldots,n+h_{s-1}d\text{ 全部为素数}
\]
的参数对数为
\[
(c+o(1))X^2/(\log X)^{s+1},\qquad c>0,
\]
并且每个端点满足 $n+h_id\equiv a_i\pmod Q$。

**证明。** 令
\[
P=\prod_{\substack{\ell\le s,\ \ell\text{ 为素数}\\\ell\ne3}}\ell.
\]
对 $i\ge1$，用中国剩余定理选择
\[
h_i\equiv(a_i-a_0)b^{-1}\pmod Q,\qquad h_i\equiv0\pmod P,
\]
再逐次加上 $QP$ 的倍数使它们严格递增。$h_0=0$。

仿射形式 $d,n+h_id$ 的方向是 $(0,1)$ 与 $(1,h_i)$，两两不成比例。模 $3$ 下所有形式是规定的单位。模 $\ell\ne3$ 下，原参数变换可逆；要求 $d\ne0$ 后，$n/d$ 必须避开 $\nu_\ell=|\{h_i\bmod\ell\}|$ 个类。若 $\ell\le s$，则 $\nu_\ell=1<\ell$；若 $\ell>s$，则 $\nu_\ell\le s<\ell$。故局部因子全部为正。

除整除某个非零 $h_i-h_j$ 的有限个素数外，$\nu_\ell=s$，局部因子为
\[
\frac{\ell^{s-1}(\ell-s)}{(\ell-1)^s}=1+O_s(\ell^{-2}).
\]
因此乘积收敛到正数。应用 (LF)，参数盒面积为 $X^2/Q^2$，即得所述计数。$\square$

### 推论 4.2（有限单项式 $F_3$ 模式）

给定有限个非零非负整数指数向量 $\mathbf e_\alpha=(e_{\alpha,0},\ldots,e_{\alpha,s-1})$，规定
\[
F_3\!\left(\prod_i x_i^{e_{\alpha,i}}\right)=f_\alpha,
\]
其中所有 $f_\alpha$ 是有限非零整数。若存在三进单位 $x_i$ 实现这些等式，且相关乘积不等于 $\pm1$，则存在某个固定的伸缩形状，使这些相同等式由无穷多组素数端点 $p_i=n+h_id$ 实现，且 $d$ 为素数。

**证明。** 取 $A>\max_\alpha|f_\alpha|$。单位乘积的 $F_3$ 值只需检查其与 $1,-1$ 之差到精度 $3^A$；有限赋值因此在相应参数类中不变。取 $a_i=x_i\bmod3^A$，对任意单位 $b$ 应用定理 4.1。正整数素数端点的非空单项式大于 $1$，所需等式全部保留。$\square$

若某个局部模式不可能由三进单位实现，自然也不可能由大于 $3$ 的素数实现。本推论不允许忽略局部相容性；形状可依赖整个目标模式。定理 1.1 另外给出了一个不随精确目标深度 $R$ 改变的特殊形状。

## 5. 适用范围

全部计数的参数 $k,R,s,A$、偏移系数和局部模式均先固定。不从这些结论推出随 $X$ 增长的精度下的统一相对误差，不将有限同余的局部比例当作任意素数抽样的独立性假设。

实际间距是固定系数乘以可变的素数 $d$。若固定 $d$，剩余的一变量形式具有成比例的线性部分，(LF) 不再适用。因此这里没有固定间距孪生素数存在性结论。

## 参考

[1] B. Green and T. Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850, Main Theorem and Corollary 1.7.
https://annals.math.princeton.edu/2010/171-3/p08

[2] B. Green and T. Tao, *The Möbius function is strongly orthogonal to nilsequences*, Annals of Mathematics 175 (2012), 541–566.
https://annals.math.princeton.edu/2012/175-2/p03

[3] B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm*, Annals of Mathematics 176 (2012), 1231–1372; corrected preprint arXiv:1009.3998v5 and the authors' erratum.
https://arxiv.org/abs/1009.3998v5

第 1–3 节只需四形式、复杂度至多 $2$ 的素数定理；第 4 节的任意有限形式数使用完整的有限复杂度版本。有限同余推导在正文中给出，不以实验计数代替证明。

# 共享素数步长的深度矩与根距离恢复

采用 [共享素数步长的高阶乘积联合深度](prime_product_correlations.md) 的固定形状。明确地，固定整数 $k,s\ge1$，置 $q=3^s$、$b=k+s$、$M=3^b$；取两两不同的非负系数
\[
\mathcal H=\{u_i,S-u_i:1\le i\le m\}\cup\{r_1,\ldots,r_{q-2}\},
\qquad \gamma=S+\sum_jr_j\not\equiv0\pmod3.
\]
这里 $m\ge2$、$0\le u_i\le S$，全部列出的系数互异，$N=|\mathcal H|=2m+q-2$。正整数 $W$ 与 $3$ 互素，并被每个不超过 $N$ 且不等于 $3$ 的素数整除。定义
\[
p_h=n+MW h d,\quad
P_i=p_{u_i}p_{S-u_i}\prod_{j=1}^{q-2}p_{r_j},\quad
D_i=F_3(P_i),\quad R_i=D_i-b,
\]
其中 $F_3(z)=v_3(z+1)-v_3(z-1)$ 对整数 $z>1$ 定义。全部形状参数在 $X\to\infty$ 之前固定。令
\[
\mathcal P(X)=\{(n,d)\in\mathbb Z^2:X<n,d\le2X,\ F_3(n)=k,
\ d,(p_h)_{h\in\mathcal H}\text{ 全为素数}\}.
\]
记 $B(X)=|\mathcal P(X)|$、$a=N+1$。$\mathbb E_X$ 和 $\Pr_X$ 表示在该有限集合中的等权平均和概率；仅在 $X$ 足够大、$B(X)>0$ 时使用。$Z=\max_iR_i$。

本文证明所有固定阶的联合深度矩收敛，并由它们恢复根距离。不对形状增长、固定步长或素数定理的有效误差作断言。

## 1. 已有的固定精度输入

上述链接的定理 2.1 给出：对每个允许的固定整数 $n$，
\[
G_{i,n}(d):=\frac{P_i+1}{M}
=A(n)+W\gamma n^{q-1}d+M H_{i,n}(d),\qquad
A(n)=\frac{n^q+1}{M}\in\mathbb Z_3^\times\cap\mathbb Z,
\]
其中 $H_{i,n}\in\mathbb Z[d]$。$G_{i,n}$ 在 $\mathbb Z_3$ 上是双射等距映射，有唯一单位零点 $\alpha_i(n)$，并且
\[
R_i=v_3(d-\alpha_i(n)),\qquad
L_{ij}:=v_3(\alpha_i(n)-\alpha_j(n))
=b+v_3(E_i-E_j),\quad E_i=u_i(S-u_i).
\tag{1.1}
\]
$L_{ij}$ 有限且与 $n$ 无关，$L_{ij}\ge b\ge2$。模 $3^t$ 的根恰有一个；所有正整数参数下 $P_i+1>0$，故 $R_i$ 有限。

在单位步长的归一化加法 Haar 模型中，记联合分布为 $\mu$。其边缘律为
\[
\mu(R_i=0)=\tfrac12,\qquad \mu(R_i=t)=3^{-t}\quad(t\ge1),
\tag{1.2}
\]
联合尾由根球的交集给出。上述链接的定理 4.1、推论 4.2 使用已知的有限复杂度线性形式素数定理 [1–3]，证明
\[
B(X)=(\kappa+o(1))X^2/(\log X)^a,\qquad \kappa>0,
\tag{1.3}
\]
以及每个固定有限向量 $\mathbf r$ 的点概率收敛
\[
\mu_X(\mathbf r):=\Pr_X((R_i)=\mathbf r)\longrightarrow\mu(\mathbf r).
\tag{1.4}
\]
这里的 $\kappa$ 取该定理的显式正 Euler 乘积。本文只使用其正性和固定形状主项，不使用任何随模数增长的线性形式素数渐近。

(1.4) 或总变差收敛本身不能推出无界矩收敛。例如 $(1-j^{-1})\delta_0+j^{-1}\delta_j$ 在总变差中趋向 $\delta_0$，均值却恒为 $1$。下面另证所需的尾控制。

## 2. 随深度增长的整数同余计数

固定输出 $i$ 及整数 $t\ge1$，令
\[
Q_t=3^{b+t},\qquad \delta_t=\frac2{3^{k+1+t}}.
\]
令 $\mathcal U_{i,t}\subset(\mathbb Z/Q_t\mathbb Z)^2$ 为条件
\[
F_3(n)=k,\qquad 3^{b+t}\mid P_i(n,d)+1
\]
确定的剩余类集合。其中 $F_3(n)=k$ 指精确的有限同余条件，不在奇异整数代表上求赋值。

### 引理 2.1

\[
|\mathcal U_{i,t}|=2\cdot3^{2b+t-k-1}=\delta_tQ_t^2=O(Q_t),
\tag{2.1}
\]
隐含常数仅依赖固定形状。所有这些类的 $d$ 都为单位。

**证明。** 允许的 $n\bmod Q_t$ 共 $2\cdot3^{b+t-k-1}$ 类。固定一个这样的类，$G_{i,n}(d)\equiv0\pmod{3^t}$ 有唯一单位根。因此 $d\bmod Q_t$ 共 $3^b$ 个提升。相乘得到结论。$n\bmod Q_t$ 足以确定 $P_i+1\bmod Q_t$，故不依赖代表选择。$\square$

令
\[
\mathcal F(n,d)=d\prod_{h\in\mathcal H}(n+MW h d).
\]
对平方自由 $e$、$(e,3)=1$，定义
\[
\rho(e)=\#\{(x,y)\bmod e:e\mid\mathcal F(x,y)\},\qquad g(e)=\rho(e)/e^2.
\]
对素数 $\ell\ne3$，若 $\nu_\ell=|\{MW h\bmod\ell:h\in\mathcal H\}|$，则
\[
\rho(\ell)=(\nu_\ell+1)\ell-\nu_\ell,\quad
0<g(\ell)<1,\quad \rho(e)\le a^{\omega(e)}e.
\tag{2.2}
\]
这里 $\omega(e)$ 不计重数。前一公式将 $y=0$ 的直线与 $\nu_\ell$ 条端点零直线求并；这些直线只在原点重合。可容许性保证 $\nu_\ell<\ell$。除有限个素数外，$\nu_\ell=N$，故
\[
g(\ell)=a/\ell-(a-1)/\ell^2.
\tag{2.3}
\]
中国剩余定理使 $\rho,g$ 在平方自由数上乘法。

### 引理 2.2（联合整除计数）

记 $A_e(X;i,t)$ 为 $X<n,d\le2X$ 中满足 $(n,d)\bmod Q_t\in\mathcal U_{i,t}$ 且 $e\mid\mathcal F(n,d)$ 的整数点数。统一于 $t,e$，
\[
A_e(X;i,t)=\delta_tX^2g(e)+r_e,
\qquad
|r_e|\ll a^{\omega(e)}(X+Q_te).
\tag{2.4}
\]

**证明。** $Q_t$ 与 $e$ 互素，合格的模 $Q_te$ 参数类恰有 $|\mathcal U_{i,t}|\rho(e)$ 个。一个参数类在边长 $X$ 的矩形中的点数与 $X^2/(Q_te)^2$ 的差的绝对值至多 $2X/(Q_te)+1$。于是
\[
|r_e|\le |\mathcal U_{i,t}|\rho(e)\bigl(2X/(Q_te)+1\bigr).
\]
代入 (2.1)–(2.2) 即得。主项系数由 (2.1) 精确给出。$\square$

## 3. 全素数集合的一致尾界

### 定理 3.1

存在依赖于固定形状的常数 $C,X_0$，使所有 $X\ge X_0$ 均有：

若 $t\ge1$ 且 $3^{b+t}\le X^{1/2}$，则
\[
\Pr_X(Z\ge t)\le C\bigl(3^{-t}+X^{-3/4}\bigr).
\tag{3.1}
\]
对所有整数 $t\ge1$，有
\[
\Pr_X(Z\ge t)\le C(\log X)^a\bigl(3^{-t}+X^{-1}\bigr).
\tag{3.2}
\]
并且每个被计数的参数点均满足
\[
0\le Z\le q\log_3X+C.
\tag{3.3}
\]

**证明。** 先证 (3.1)。在引理 2.2 的整数序列上应用经典 Selberg 上界筛 [4, Theorem 13.1]，筛素数取全部 $\ell\ne3$。其局部函数满足 (2.2)–(2.3)。取平方权支撑小于
\[
z=X^{1/16},\qquad D=z^2=X^{1/8}.
\]
所用外部定理的具体形式为
\[
S(X;z)\le \frac{\delta_tX^2}{H(z)}
+\sum_{e<D}^{*}3^{\omega(e)}|r_e|,
\quad H(z)=\sum_{e<z}^{*}\prod_{\ell\mid e}\frac{g(\ell)}{1-g(\ell)}.
\tag{3.4}
\]
星号只取平方自由且与 $3$ 互素的整数。合成权界来自最优平方权的 $|\rho_d|\le1$ 及每个素因子在最小公倍数中的三种分配。由 (2.3)，标准乘法函数估计 [5, §14.2] 给出 $H(z)\asymp(\log z)^a$；有限个例外素数仅改变正常数。所有目标素数值均大于 $X>z$，所以目标集合包含于该预筛集合。

由 (2.4) 以及
\[
\sum_{e<D}(3a)^{\omega(e)}\ll D(1+\log D)^{3a-1},
\]
有
\[
\sum_{e<D}^{*}3^{\omega(e)}|r_e|
\ll(XD+Q_tD^2)(1+\log D)^{3a-1}.
\tag{3.5}
\]
这里可用 $(3a)^{\omega(e)}\le\tau_{3a}(e)$ 和约数函数的初等求和界。若 $Q_t\le X^{1/2}$，则 (3.5) 至多为 $O(X^{9/8}(\log X)^{3a-1})$。故固定输出的素数尾计数满足
\[
\#\{(n,d)\in\mathcal P(X):R_i\ge t\}
\ll\frac{X^2}{3^t(\log X)^a}+X^{9/8}(\log X)^{3a-1}.
\]
除以 (1.3)，得到
\[
\Pr_X(R_i\ge t)\ll3^{-t}+X^{-7/8}(\log X)^{4a-1}
\ll3^{-t}+X^{-3/4}.
\]
对固定的 $m$ 个输出求并，得到 (3.1)。此处仅使用 (1.3) 的固定形状总计数，不使用增长精度下的素数渐近。

对 (3.2)，去掉全部素性要求。固定每个整数 $n$，$R_i\ge t$ 将 $d$ 限制在模 $3^t$ 的一个类，因此整数点数不超过
\[
(X+1)(X/3^t+1)\ll X^23^{-t}+X.
\]
再除以 (1.3) 并对输出求并。最后，每个 $P_i+1$ 为正且至多为常数乘以 $X^q$，因此其三进赋值不超过 $q\log_3X+O(1)$，得到 (3.3)。$\square$

## 4. 指数加权总变差与全部固定阶矩

### 定理 4.1

对每个固定 $0<\eta<1/q$，有
\[
\boxed{\sum_{\mathbf r\in\mathbb Z_{\ge0}^{m}}
3^{\eta\max_i r_i}|\mu_X(\mathbf r)-\mu(\mathbf r)|\longrightarrow0.}
\tag{4.1}
\]
因此，对每个固定多元多项式 $F$，
\[
\mathbb E_X F(R_1,\ldots,R_m)\longrightarrow
\int F(\mathbf r)\,d\mu(\mathbf r).
\tag{4.2}
\]
同样结论适用于满足 $|F(\mathbf r)|\le C_F3^{\eta\max r_i}$ 的任意固定函数，其中 $0<\eta<1/q$。

**证明。** 先对任意固定 $0<\theta<1/q$ 证明
\[
\sup_{X\ge X_1}\mathbb E_X3^{\theta Z}<\infty.
\tag{4.3}
\]
取 $T_0=\lfloor\tfrac12\log_3X\rfloor-b$，则 $3^{T_0}\asymp X^{1/2}$，常数允许依赖 $b$。整数非负变量的尾求和给出
\[
\mathbb E_X3^{\theta Z}
=1+\sum_{t\ge1}(3^{\theta t}-3^{\theta(t-1)})\Pr_X(Z\ge t).
\]
在 $1\le t\le T_0$ 使用 (3.1)，和至多为一个收敛几何级数加
$O(X^{-3/4+\theta/2})$。在 $t>T_0$ 使用 (3.2)，并由 (3.3) 在 $q\log_3X+O(1)$ 处截断，所得上界为
\[
O_\theta\!\left((\log X)^a
\left[X^{-(1-\theta)/2}+X^{q\theta-1}\right]\right)=o(1).
\]
这里 $\theta<1/q\le1/3$ 使所有指数为负，故 (4.3) 成立。

局部分布满足 $\mu(Z\ge t)\le m/(2\cdot3^{t-1})$，因而对所有 $\theta<1$，$\int3^{\theta Z}\,d\mu<\infty$。给定 $\eta<1/q$，取 $\eta<\theta<1/q$。在 $Z>K$ 上，
\[
3^{\eta Z}\le3^{-(\theta-\eta)K}3^{\theta Z}.
\]
因此两个模型的加权盒外质量统一随 $K\to\infty$ 趋零。在有限盒 $\{0,\ldots,K\}^m$ 内使用 (1.4) 的逐点收敛，再令 $K\to\infty$，得到 (4.1)。多项式增长被任一正指数权控制，故 (4.2) 及最后的结论随之成立。$\square$

这是固定形状下的加权分布收敛。指数范围 $\eta<1/q$ 来自 (3.2)–(3.3) 的粗界，不声称最优；局部模型自身的指数矩允许 $\eta<1$。本证明不提供总计数 (1.3) 的有效误差，也不保证深度随 $X$ 增长时有统一相对主项或非空。

## 5. 均值、协方差与根树恢复

### 定理 5.1

对每个输出 $i$，
\[
\lim_{X\to\infty}\mathbb E_XD_i=b+\frac34,
\qquad
\lim_{X\to\infty}\operatorname{Var}_X(D_i)=\frac{15}{16}.
\tag{5.1}
\]
对不同输出 $i,j$，有
\[
\boxed{\lim_{X\to\infty}\mathbb E_X(D_i-D_j)^2=3^{1-L_{ij}},}
\tag{5.2}
\]
\[
\boxed{\lim_{X\to\infty}\operatorname{Cov}_X(D_i,D_j)
=\frac{15}{16}-\frac32\,3^{-L_{ij}},}
\tag{5.3}
\]
\[
\lim_{X\to\infty}\operatorname{Corr}_X(D_i,D_j)
=1-\frac85\,3^{-L_{ij}}.
\tag{5.4}
\]

**证明。** 先在局部模型计算。由 (1.2)，
\[
\mathbb ER_i=\sum_{t\ge1}t3^{-t}=\tfrac34,
\quad\mathbb ER_i^2=\sum_{t\ge1}t^23^{-t}=\tfrac32,
\quad\operatorname{Var}(R_i)=\tfrac{15}{16}.
\]
置 $L=L_{ij}$。两根距离的非阿基米德性质保证 $R_i\ne R_j$ 时，较小者恰为 $L$。对每个 $t\ge1$，
\[
\Pr(R_i=L+t,R_j=L)=3^{-(L+t)},
\quad\Pr(R_i=L,R_j=L+t)=3^{-(L+t)}.
\]
因此
\[
\mathbb E(R_i-R_j)^2
=2\cdot3^{-L}\sum_{t\ge1}t^23^{-t}=3^{1-L}.
\]
两个变量均值相同，所以其协方差为 $15/16$ 减去差平方期望的一半。除以边缘方差得到相关系数。定理 4.1 将这些无界一、二阶矩转移到全素数模型；方差极限严格为正，故相关系数最终有定义且收敛。$\square$

### 推论 5.2（由二阶统计恢复完整联合律）

令 $\Sigma_{ij}=\lim_X\operatorname{Cov}_X(D_i,D_j)$。则对于 $i\ne j$，
\[
3^{-L_{ij}}=\frac23\left(\frac{15}{16}-\Sigma_{ij}\right)
=\frac13\lim_X\mathbb E_X(D_i-D_j)^2.
\tag{5.5}
\]
因此，在本固定共享根模型中，带标签的极限协方差矩阵确定全部 $L_{ij}$，继而由所引用文稿的定理 3.2 确定整个深度向量的联合分布与精确模式可实现性。

**证明。** (5.5) 直接解出 (5.3)；函数 $L\mapsto3^{-L}$ 单射。先验根模型中的精确联合概率只使用距离矩阵及固定 $b$，故可恢复。$\square$

这里恢复的是根间距离及其树状关系，不是各个 $\alpha_i(n)$ 的绝对位置。它也不是“单次输入的两两乘积 $F_3$ 值决定全部高阶输出”的结论；极限协方差是对整个固定全素数族的统计资料，并依赖已知的共享根模型。

另一个等价的几何表达是：对单位根 $\alpha$，函数
\[
f_\alpha(d)=v_3(d-\alpha)-3/4
\]
属于单位域上的 $L^2$，并满足
\[
\|f_\alpha-f_\beta\|_2^2=3|\alpha-\beta|_3.
\]
这是上述积分公式的直接重述，不是对新的非阿基米德空间结构的主张。

## 6. 正相关与深层互斥

在所引用文稿的六素数形状
\[
\mathcal H=\{0,1,2,3,5\},\quad p_h=n+90hd,\quad
D_1=F_3(p_0p_3p_5),\quad D_2=F_3(p_1p_2p_5)
\]
中，$b=2,L_{12}=2$。所以
\[
\lim\mathbb E_XD_i=\frac{11}{4},\quad
\lim\operatorname{Cov}_X(D_1,D_2)=\frac{37}{48},\quad
\lim\operatorname{Corr}_X(D_1,D_2)=\frac{37}{45},
\]
\[
\lim\mathbb E_X(D_1-D_2)^2=\frac13.
\]
同时，确定性有 $\min(D_1,D_2)\le4$。两个事件 $D_1>4,D_2>4$ 各自的极限概率为 $1/18$，交集为空，所以其指示变量的协方差极限为 $-1/324$。这不与原深度变量的正协方差矛盾。

对于根间距离均为 $3$ 的八素数形状，任意两输出的相关系数极限为 $127/135$，但三个精确要求 $D_i=5$ 仍然不相容。二阶统计可恢复完整联合律，并不等于变量相互独立。

最后，若 $a_t$ 为根模 $3^t$ 的不同类数，$L_*=\max_{i\ne j}L_{ij}$，则定理 4.1 和局部尾计数还给出
\[
\lim_X\mathbb E_X\max_iD_i
=b+\sum_{t=1}^{L_*}\frac{a_t}{2\cdot3^{t-1}}
+\frac{3m}{4}\,3^{-L_*}.
\]
六素数形状中该值为 $17/6$；三个等距根的八素数形状中为 $101/36$。

## 参考

[1] B. Green and T. Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850.
https://annals.math.princeton.edu/2010/171-3/p08

[2] B. Green and T. Tao, *The Möbius function is strongly orthogonal to nilsequences*, Annals of Mathematics 175 (2012), 541–566.
https://annals.math.princeton.edu/2012/175-2/p03

[3] B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm*, Annals of Mathematics 176 (2012), 1231–1372; corrected preprint arXiv:1009.3998v5.
https://arxiv.org/abs/1009.3998v5

[4] K. S. Kedlaya, *Notes on analytic number theory*, Chapter 13, Theorem 13.1, (13.2.3)–(13.2.5), Exercise 13.3.2.
https://kskedlaya.org/ant/chap-selberg.html

[5] K. S. Kedlaya, *Notes on analytic number theory*, Chapter 14, §14.2, (14.2.1).
https://kskedlaya.org/ant/chap-selberg2.html

本文使用已有的素数总计数与固定精度分布作为输入，另给出一致尾界与矩传递证明。全部文稿均为书面数学证明，不等同于 Lean 内核验证。

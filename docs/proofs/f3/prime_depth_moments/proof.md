# F3-MOM：完整书面证明（更新稿）

状态：`PAPER-AUDITED`。以下正文按更新后的研究稿 `prime_depth_moments.md` 保存。

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

本文证明指数加权分布及所有固定阶的联合深度矩收敛，由它们恢复根距离，并给出联合概率生成函数的有限有理表示。不对形状增长、固定步长或素数定理的有效误差作断言。

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


### 定理 3.2（素数乘积的单射性与极深尾部）

固定任一输出 $P_i$。在 $\mathcal P(X)$ 上，映射 $(n,d)\mapsto P_i(n,d)$ 是单射。存在仅依赖固定形状的常数 $C_1$，使全部整数 $t\ge1$ 都满足
\[
\Pr_X(Z\ge t)\le C_1(\log X)^a
\min\{3^{-t}+X^{-1},\ X^{q-2}3^{-t}\}.
\tag{3.6}
\]
特别地，右边可以放宽为
\[
C_1(\log X)^a\left(3^{-t}+\min\{X^{-1},X^{q-2}3^{-t}\}\right).
\tag{3.7}
\]

**证明。** 将这个输出使用的 $q$ 个偏移排序为 $H_1<\cdots<H_q$，其素数因子相应为 $n+MW H_jd$。因 $d>0$，这些因子严格递增，且都为素数。若两个参数点产生同一乘积，则素数唯一分解及排序给出每个对应因子相等。前两个因子已确定
\[
d=\frac{p_{H_2}-p_{H_1}}{MW(H_2-H_1)},\qquad n=p_{H_1}-MW H_1d.
\]
因此参数相同。证明不要求某个 $H_j$ 等于零，也不需要将分解计算看成一个高效算法。

在当前参数盒中，$0<P_i+1\le C_iX^q$。条件 $R_i\ge t$ 要求 $P_i+1$ 为 $3^{b+t}$ 的正倍数。这些倍数至多有 $\lfloor C_iX^q/3^{b+t}\rfloor$ 个，且每个乘积至多来自一个参数点。因此
\[
\#\{(n,d)\in\mathcal P(X):R_i\ge t\}\ll X^q3^{-t}.
\]
这里没有 $+1$ 舍入项，因为从第一个正倍数开始计数。对输出求并并除以 (1.3)，得到 $C(\log X)^aX^{q-2}3^{-t}$。与 (3.2) 取较小者得 (3.6)。最后使用 $\min(A+B,C)\le A+\min(B,C)$ 得 (3.7)。$\square$

该论证使用完整的乘积整数及其素数唯一分解，不是从单个 $F_3(P_i)$ 数值恢复参数；也没有将整数或几乎素数因子当作素数使用。

## 4. 指数加权总变差与全部固定阶矩

### 定理 4.1

对每个固定 $0<\eta<1/(q-1)$，有
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
同样结论适用于满足 $|F(\mathbf r)|\le C_F3^{\eta\max r_i}$ 的任意固定函数，其中 $0<\eta<1/(q-1)$。

**证明。** 先对任意固定 $0<\theta<1/(q-1)$ 证明
\[
\sup_{X\ge X_1}\mathbb E_X3^{\theta Z}<\infty.
\tag{4.3}
\]
取
\[
T_0=\left\lfloor\tfrac12\log_3X\right\rfloor-b,\qquad
T_1=\lfloor(q-1)\log_3X\rfloor.
\]
对足够大的 $X$，有 $1\le T_0<T_1$。非负整数变量的尾求和给出
\[
\mathbb E_X3^{\theta Z}
=1+\sum_{t\ge1}(3^{\theta t}-3^{\theta(t-1)})\Pr_X(Z\ge t).
\]
在 $t\le T_0$ 使用 (3.1)，所得上界是一个收敛几何级数加 $O(X^{-3/4+\theta/2})$。在 $T_0<t\le T_1$ 使用 (3.2)，贡献为
\[
O_\theta\left((\log X)^a
\left[X^{-(1-\theta)/2}+X^{-1+(q-1)\theta}\right]\right).
\]
在 $t>T_1$ 使用定理 3.2 中的新上界，贡献至多
\[
C(\log X)^aX^{q-2}\sum_{t>T_1}3^{-(1-\theta)t}
\ll_\theta(\log X)^aX^{-1+(q-1)\theta}.
\]
这里 $0<\theta<1/(q-1)\le1/2$ 使所有余项趋零。因此 (4.3) 成立。这一论证不需要把最后一段截断在 (3.3) 的大小上界。

局部分布满足 $\mu(Z\ge t)\le m/(2\cdot3^{t-1})$，因而对所有 $\theta<1$ 有 $\int3^{\theta Z}\,d\mu<\infty$。给定 $\eta<1/(q-1)$，取 $\eta<\theta<1/(q-1)$。在 $Z>K$ 上，
\[
3^{\eta Z}\le3^{-(\theta-\eta)K}3^{\theta Z}.
\]
因此两个模型的加权盒外质量统一随 $K\to\infty$ 趋零。在有限盒 $\{0,\ldots,K\}^m$ 内使用 (1.4) 的逐点收敛，再令 $K\to\infty$，得到 (4.1)。多项式增长被任一正指数权控制，故 (4.2) 及最后的结论随之成立。$\square$

这是固定形状下的加权分布收敛。指数范围 $\eta<1/(q-1)$ 是充分范围，不声称最优；局部模型自身的指数矩允许 $\eta<1$。本证明不提供总计数 (1.3) 的有效误差，也不保证深度随 $X$ 增长时有统一相对主项或非空。

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


## 7. 有限部分与单坐标几何尾

置 $K=\max_{i\ne j}L_{ij}$，并约定 $L_{ii}=+\infty$。$K$ 为固定的有限整数。以下局部结论对每个允许的固定 $n$ 成立，其分布与 $n$ 无关。

### 引理 7.1（极深层至多一个坐标变化）

对每个有限深度向量，最多只有一个 $R_i>K$。若 $R_i=u>K$，则所有 $j\ne i$ 均有 $R_j=L_{ij}$，且该精确向量的局部概率为 $3^{-u}$。在整数全素数模型中也有同样的确定性支撑限制。特别地，
\[
\sum_iR_i\le Z+(m-1)K.
\tag{7.1}
\]

**证明。** 两个坐标若都大于 $K$，则两根相差的赋值也大于 $K$，与其定义矛盾。若 $R_i=u>K\ge L_{ij}$，不等赋值相加法则给出 $v_3(d-\alpha_j)=L_{ij}$。事件因而等价于 $R_i=u$，其概率由 (1.2) 为 $3^{-u}$。若全部坐标不超过 $K$，(7.1) 同样显然。$\square$

### 定理 7.2（多元有理生成函数）

令 $\mathbf z^{\mathbf r}=\prod_i z_i^{r_i}$，并定义
\[
\Phi(\mathbf z)=\mathbb E_\mu\mathbf z^{\mathbf R},\qquad
A_K(\mathbf z)=\sum_{0\le r_i\le K}\mu(\mathbf r)\mathbf z^{\mathbf r}.
\]
在多圆盘 $|z_i|<3$ 内，这些期望绝对收敛，且
\[
\boxed{
\Phi(\mathbf z)=A_K(\mathbf z)+
\sum_{i=1}^m
\left(\prod_{j\ne i}z_j^{L_{ij}}\right)
\frac{(z_i/3)^{K+1}}{1-z_i/3}.
}\tag{7.2}
\]
这是有理系数的有理函数，其分母整除 $\prod_i(1-z_i/3)$。$A_K$ 及全部尾项仅由带标签的矩阵 $(L_{ij})$ 决定。

**证明。** 引理 7.1 将分布拆成有限盒内部分，以及 $m$ 条互不相交的尾部射线。在第 $i$ 条射线上，其他坐标固定为 $L_{ij}$，第 $i$ 坐标的质量为 $3^{-u}$，$u=K+1,K+2,\ldots$。分别求几何级数即得。精确层概率是有理数，见所引用文稿定理 3.2；绝对收敛也由这有限个几何级数直接给出。$\square$

有限多项式无需枚举全部 $(K+1)^m$ 个向量。对 $1\le t\le K$，令 $\mathscr C_t$ 为由 $L_{ij}\ge t$ 给出的根簇划分。对 $C\in\mathscr C_t$，取任意代表 $a_C$，令 $c(C)$ 为 $C$ 包含的 $\mathscr C_{t+1}$ 子簇数，定义
\[
r_i(C,t)=\min(t,L_{a_Ci}).
\]
则
\[
\boxed{
A_K(\mathbf z)=\frac12+
\sum_{t=1}^K\sum_{C\in\mathscr C_t}
\frac{3-c(C)}{2\cdot3^t}\prod_i z_i^{r_i(C,t)}.
}\tag{7.3}
\]
表达式至多有 $1+mK$ 个有限项，允许合并相同单项式及删去零系数。

**证明。** 所有根属于同一个单位首位类，另一个首位类给出零向量及质量 $1/2$。深度 $t$ 的每个根簇对应一个父球；其 $3-c(C)$ 个不含根的子球上，全部深度恒等于 $r_i(C,t)$，每个子球的单位域测度为 $1/(2\cdot3^t)$。沿根树遍历，未进入超过 $K$ 的根邻域的点恰好落入这些互不相交的空子球。根距性质保证向量不依赖代表选择。$\square$

### 推论 7.3（总深度的最终精确尾律）

令 $S_0=\sum_iR_i$、$s_i=\sum_{j\ne i}L_{ij}$。则
\[
\mathbb E_\mu z^{S_0}
=A_K(z,\ldots,z)+
\frac{(z/3)^{K+1}}{1-z/3}\sum_i z^{s_i}.
\tag{7.4}
\]
对每个整数 $r>mK$，恰有
\[
\boxed{\mu(S_0=r)=3^{-r}\sum_i3^{s_i}.}\tag{7.5}
\]
因此对实数 $z>0$，$\mathbb E_\mu z^{S_0}$ 有限当且仅当 $z<3$。作为有理函数，它在 $z=3$ 具有简单极点，且
\[
\lim_{z\uparrow3}(1-z/3)\mathbb E_\mu z^{S_0}=\sum_i3^{s_i}>0.
\]

**证明。** 在 (7.2) 中令所有变量为 $z$。有限多项式的总次数至多为 $mK$；当 $r>mK$ 时，第 $i$ 条射线唯一的对应坐标为 $u=r-s_i>K$，其质量为 $3^{-u}$。相加得到 (7.5)。其余断言由正系数几何尾直接得到。$\square$

式 (7.5) 是局部模型的精确等式；对于全素数模型，它给出每个预先固定的 $r$ 的极限比例，不是允许 $r$ 随 $X$ 增长的统一渐近。

## 8. 全素数生成函数及一个明确的指数平均

定义有限多项式
\[
\Phi_X(\mathbf z)=\mathbb E_X\prod_i z_i^{R_i},
\]
按多项式约定 $z_i^0=1$，包括 $z_i=0$ 的情形。

### 定理 8.1

在多圆盘
\[
|z_i|<3^{1/(q-1)}\qquad(1\le i\le m)
\]
内，$\Phi_X$ 在紧集上一致收敛到定理 7.2 的有理函数 $\Phi$。其任意固定阶复偏导数也在紧集上一致收敛。

**证明。** 给定紧集，取 $1<R<3^{1/(q-1)}$，使其全部坐标绝对值不超过 $R$。两个模型均有支撑限制 (7.1)，所以
\[
|\mathbf z^{\mathbf r}|\le R^{(m-1)K}R^{\max r_i}.
\]
因此
\[
\sup|\Phi_X-\Phi|\le R^{(m-1)K}
\sum_{\mathbf r}3^{(\log_3R)\max r_i}|\mu_X(\mathbf r)-\mu(\mathbf r)|\to0
\]
由定理 4.1。导数结论是在略大的紧多圆盘上应用 Cauchy 积分公式。$\square$

该多圆盘条件分别约束每个坐标，不要求 $\sum_i\log_3|z_i|<1/(q-1)$；原因是足够深处只有一个坐标能够继续增长。局部函数的绝对收敛范围 $|z_i|<3$ 大于此处已证明的素数收敛范围，不可混同。

### 六素数形状

采用第 6 节的 $b=2,L_{12}=K=2$。写 $R_i=D_i-2$，则
\[
\Phi(z_1,z_2)=\frac12+\frac{z_1z_2}{3}+\frac{z_1^2z_2^2}{18}
+z_2^2\frac{(z_1/3)^3}{1-z_1/3}
+z_1^2\frac{(z_2/3)^3}{1-z_2/3}.
\tag{8.1}
\]
从而
\[
\mathbb E_\mu z^{R_1+R_2}=\frac12+\frac{z^2}{3}+\frac{z^4}{18}
+\frac{2z^5}{27(1-z/3)},
\quad
\mathbb E_\mu z^{\max(R_1,R_2)}=\frac12+\frac z3+\frac{z^2}{18}
+\frac{2z^3}{27(1-z/3)}.
\]
由于 $\log_3(3/2)<1/2=1/(q-1)$，定理 8.1 和定理 4.1 分别给出
\[
\boxed{
\lim_{X\to\infty}\mathbb E_X(3/2)^{D_1+D_2-4}=\frac{85}{32},\qquad
\lim_{X\to\infty}\mathbb E_X(3/2)^{\max(D_1,D_2)-2}=\frac{13}{8}.
}\tag{8.2}
\]
另外，对每个固定整数 $r\ge5$，
\[
\lim_X\Pr_X(D_1+D_2-4=r)=18\cdot3^{-r}.
\]

若将两个边缘相同的局部变量误当作独立，其单变量生成函数为 $(3+z)/(2(3-z))$，和的生成函数具有二阶极点。实际共享根模型 (8.1) 只有一个简单极点。这里的区别来自有限分支之后的单坐标尾部，而不是独立性近似。

### 生成函数的既有背景

从根的有限三进展开建立树状结构，再求一元局部 zeta 函数的有理表达，已有直接文献 [6]；一元多项式的一般计算结果另见 [7]。这里不将有理性本身声明为新的原理。本文给出该固定共享根模型的多元公式，并通过另行证明的指数尾界，建立其全素数平均在指定多圆盘内的收敛。

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

[6] W. A. Zúñiga-Galindo, *Computing Igusa's local zeta functions of univariate polynomials, and linear feedback shift registers*, arXiv:math/0204360.
https://arxiv.org/abs/math/0204360

[7] A. Dwivedi and N. Saxena, *Computing Igusa's local zeta function of univariates in deterministic polynomial-time*, arXiv:2006.08926.
https://arxiv.org/abs/2006.08926

本文使用已有的素数总计数与固定精度分布作为输入，另给出一致尾界、唯一分解尾界、矩传递及生成函数证明。全部文稿均为书面数学证明，不等同于 Lean 内核验证。
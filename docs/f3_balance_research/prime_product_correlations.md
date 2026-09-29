# 共享素数步长的高阶乘积联合深度

对整数 $z>1$，定义
\[
F_3(z)=v_3(z+1)-v_3(z-1).
\]
整数赋值自变量均非零。使用 $\mathbb Z_3$ 时，零的赋值取 $+\infty$。所有素数计数中的层级、系数、形式数和阈值先固定，再令 $X\to\infty$。计数使用已知的有限复杂度线性形式素数定理，而不是素数事件独立性假设。

## 1. 共同因子与固定系数和

固定 $k,s\ge1$，置
\[
q=3^s,\qquad b=k+s,\qquad M=3^b.
\]
取 $m\ge2$ 组系数。固定非负整数 $S,r_1,\ldots,r_{q-2}$ 和 $0\le u_i\le S$，$1\le i\le m$，要求集合
\[
\mathcal H=\{u_i,S-u_i:1\le i\le m\}\cup\{r_1,\ldots,r_{q-2}\}
\]
中的全部列出系数互不相同，并要求
\[
\gamma=S+\sum_{j=1}^{q-2}r_j\not\equiv0\pmod3.
\]
令 $N=|\mathcal H|=2m+q-2$。先取任意正整数 $W$ 且 $3\nmid W$。对 $n>1,d>0$、$F_3(n)=k$、$3\nmid d$，定义
\[
p_h=n+MW h d\quad(h\in\mathcal H),\qquad
P_i=p_{u_i}p_{S-u_i}\prod_{j=1}^{q-2}p_{r_j},\qquad
D_i=F_3(P_i).
\]
每个 $P_i$ 含有 $q$ 个不同端点；不同输出共享 $q-2$ 个因子。记
\[
E_i=u_i(S-u_i).
\]
由系数互异可知 $E_i\ne E_j$：若 $E_i=E_j$，则 $u_i=u_j$ 或 $u_i=S-u_j$。

### 引理 1.1（低次数数据）

对于全部 $N$ 个端点的任一非空单项式 $V=\prod_{h\in\mathcal H}p_h^{e_h}$，若 $1\le a:=\sum_h e_h<q$，则
\[
F_3(V)=(-1)^{a+1}\bigl(k+v_3(a)\bigr).
\tag{1.1}
\]

**证明。** 所有端点同余于 $n\pmod M$，故 $V\equiv n^a\pmod M$。置 $U=-n\equiv1\pmod3$，则 $v_3(U-1)=k$。几何和及逐次立方给出 $v_3(U^a-1)=k+v_3(a)$，具体证明见 [算术结构](arithmetic.md) 定理 1.2。由于 $a<3^s$，这个赋值严格小于 $b$，不会被模 $M$ 的扰动改变。符号由 $V\equiv(-1)^a\pmod3$ 决定。$\square$

## 2. 根坐标及根间距

### 定理 2.1

对每个允许的固定 $n$，存在唯一的单位 $\alpha_i(n)\in\mathbb Z_3^\times$，使对全部允许的正整数 $d$，
\[
D_i=b+v_3(d-\alpha_i(n)).
\tag{2.1}
\]
并且对 $i\ne j$，有精确等式
\[
\boxed{v_3(\alpha_i(n)-\alpha_j(n))=b+v_3(E_i-E_j).}
\tag{2.2}
\]
根间距不依赖 $n$。记右边为 $L_{ij}$。

**证明。** 由引理 1.1 中的幂估值论证，
\[
A(n)=\frac{n^q+1}{M}\in\mathbb Z_3^\times\cap\mathbb Z.
\]
展开每个乘积，一次系数之和均为 $\gamma$，故
\[
G_i(d):=\frac{P_i+1}{M}
=A(n)+W\gamma n^{q-1}d+M H_i(d),\qquad H_i\in\mathbb Z[d].
\tag{2.3}
\]
$H_i$ 只含次数至少为 $2$ 的项。模 $3$ 下，这是常数和斜率均为单位的仿射函数，其唯一零点不是 $0$。对每个目标值，模 $3$ 的唯一原像因导数为单位而逐次唯一提升；因此 $G_i$ 在每个模 $3^T$ 上都是置换，并在 $\mathbb Z_3$ 上为双射。另有
\[
G_i(d)-G_i(e)=(d-e)\bigl(W\gamma n^{q-1}+M K_i(d,e)\bigr),
\]
括号为单位，所以 $G_i$ 等距。取其唯一零点 $\alpha_i$，即得 (2.1)。$P_i\equiv-1\pmod3$，且对正整数输入 $P_i+1>0$，故整数表达式没有奇异点。

置 $x=MWd$，$Q(d)=\prod_{j=1}^{q-2}(n+r_jx)$。由
\[
(n+u_ix)(n+(S-u_i)x)=n^2+Snx+E_ix^2
\]
得到
\[
\boxed{G_i(d)-G_j(d)=MW^2(E_i-E_j)d^2Q(d).}
\tag{2.4}
\]
代入 $d=\alpha_j$。由于 $\alpha_j$ 为单位且 $Q(\alpha_j)\equiv n^{q-2}\not\equiv0\pmod3$，右边赋值为 $b+v_3(E_i-E_j)$。左边等于 $G_i(\alpha_j)-G_i(\alpha_i)$，使用等距性得到 (2.2)。$\square$

### 推论 2.2（确定性限制）

对任意 $i\ne j$，
\[
\min(D_i,D_j)\le b+L_{ij}=2b+v_3(E_i-E_j).
\tag{2.5}
\]
若 $D_i\ne D_j$，则这里取等号；若其中一项小于右边，则两项相等。

**证明。** 两个根坐标之差为 $\alpha_j-\alpha_i$。使用非阿基米德三角不等式及不等赋值时的等号条件即可。也可在正整数参数上直接对 (2.4) 使用同一论证。$\square$

## 3. 完整的联合阈值公式

对每个固定允许的 $n$，在 $\mathbb Z_3^\times$ 上按归一化加法 Haar 测度选择 $d$。同样的概率可理解为任意足够高的有限模数上的单位类比例。

### 定理 3.1

给定 $t_1,\ldots,t_m\ge0$，令 $T=\max_i t_i$。则
\[
\boxed{
\Pr(D_i\ge b+t_i\ \forall i)=
\begin{cases}
1,&T=0,\\
\dfrac1{2\cdot3^{T-1}},&T\ge1\text{ 且 }\min(t_i,t_j)\le L_{ij}\ \forall i\ne j,\\
0,&\text{否则}.
\end{cases}}
\tag{3.1}
\]
右边与 $n$ 的具体值无关。任意有限个精确深度事件，由该联合尾式逐坐标作有限差分得到。

**证明。** 正门槛的条件等价于 $d\equiv\alpha_i(n)\pmod{3^{t_i}}$。这些素数幂模数的同余两两相容，当且仅当 $\alpha_i\equiv\alpha_j\pmod{3^{\min(t_i,t_j)}}$，由定理 2.1 恰为所列条件。相容时交集是一个模 $3^T$ 的单位类。单位域的加法 Haar 测度为 $2/3$，而该类测度为 $3^{-T}$，故条件比例为 $1/(2\cdot3^{T-1})$。$T=0$ 时没有条件。$\square$

特别地，单个输出的边缘律是
\[
\Pr(D_i=b)=\frac12,\qquad \Pr(D_i=b+t)=3^{-t}\quad(t\ge1).
\tag{3.2}
\]
具有相同边缘律不表示输出独立；全部联合依赖由有限距离矩阵 $(L_{ij})$ 给出。

## 4. 真正全素数配置中的计数

本节另要求 $W$ 被每个不超过 $N$ 且不等于 $3$ 的素数整除。设 $\mathcal P(X)$ 为
\[
X<n,d\le2X,\quad F_3(n)=k,\quad d,\ (p_h)_{h\in\mathcal H}\text{ 全部为素数}
\]
的整数参数集合。取 $X>3$，则 $3\nmid d$ 自动满足。

采用 Green–Tao–Ziegler 理论的以下已知结论 [1–3]：固定的整数仿射线性形式，若线性部分两两不成比例，则在所有形式为正且与 $X$ 同阶的凸盒中，同时取素数的计数为
\[
\left(\prod_\ell\beta_\ell+o(1)\right)
\frac{\operatorname{area}(K_X)}{(\log X)^a},\qquad
\beta_\ell=\ell^{-2}\sum_{u,v\bmod\ell}\prod_{j=1}^a
\frac\ell{\ell-1}\mathbf1_{\ell\nmid\psi_j(u,v)}.
\tag{LF}
\]
$a$ 为形式数。一般有限复杂度使用 [1] 的框架及 [2–3] 的完整输入，不能只依赖 [1] 当时已经无条件证明的复杂度至多 $2$ 情形。从加权版本得到素数指示版本，可先排除高次素数幂：一个非恒定形式取高次素数幂的参数点数为 $O(X^{3/2}\log X)$，其加权贡献为 $o(X^2)$；其余各对数权均为 $\log X+O(1)$。

令
\[
\nu_\ell=|\{MW h\bmod\ell:h\in\mathcal H\}|,
\quad
\mathfrak S=\left(\frac32\right)^{N+1}
\prod_{\ell\ne3}\frac{\ell^{N-1}(\ell-\nu_\ell)}{(\ell-1)^N},
\quad \kappa=\frac4{3^{k+2}}\mathfrak S.
\]

### 定理 4.1

$\kappa>0$，且
\[
|\mathcal P(X)|=(\kappa+o(1))\frac{X^2}{(\log X)^{N+1}}.
\tag{4.1}
\]
对定理 3.1 的任一固定阈值向量，设其右边为 $\rho(\mathbf t)$，则
\[
\#\{(n,d)\in\mathcal P(X):D_i\ge b+t_i\ \forall i\}
=(\kappa\rho(\mathbf t)+o(1))\frac{X^2}{(\log X)^{N+1}}.
\tag{4.2}
\]
不相容时，计数实际上恒为零。每个严格正的固定有限类事件都有无穷多个全素数实现。

**证明。** 固定足够大的 $A$，令 $Q=3^A$，并固定允许的参数类 $(n,d)\equiv(a_0,b_0)\pmod Q$。可取 $A\ge b+T+1$，它足以判定所有阈值和所需精确事件。代入 $n=a_0+Qx,d=b_0+Qy$。$N+1$ 个形式的方向是 $(0,1)$ 和 $(1,MW h)$，两两不成比例；用其余形式各自成组，可知复杂度至多 $N-1$。

在模 $3$ 下所有形式为单位，局部因子为 $(3/2)^{N+1}$。在 $\ell\ne3$ 处参数变换可逆；要求 $d\ne0$ 后，$n/d$ 必须避开 $\nu_\ell$ 个类，故合格参数数为 $(\ell-1)(\ell-\nu_\ell)$，给出所列局部因子。若 $\ell\le N$、$\ell\ne3$，则 $\ell\mid W$，所以 $\nu_\ell=1$；若 $\ell>N$，则 $\nu_\ell\le N<\ell$。所有因子均为正。除整除某个非零偏移差的有限个素数外，$\nu_\ell=N$，尾因子为 $1+O_N(\ell^{-2})$。因此 $\mathfrak S>0$。

每个允许参数类的主系数相同，等于 $\mathfrak S/Q^2$。模 $Q$ 的基础参数类数为
\[
(2\cdot3^{A-k-1})(2\cdot3^{A-1})=4\cdot3^{2A-k-2}.
\]
对固定有限个类求和即得 (4.1)。固定每一个 $n$ 类时，定理 3.1 给出相同的单位 $d$ 类比例 $\rho(\mathbf t)$，所以再次逐类求和得到 (4.2)。精确事件通过有限差分处理；若其类比例严格为正，则相应主系数严格为正。$\square$

## 5. 任意指定的双输出分界

取 $\tau\ge0$，令 $v=2\cdot3^\tau$。在第 1 节取
\[
S=v+1,\quad u_1=0,\quad u_2=1,\quad r_j=v+3j\quad(1\le j\le q-2).
\]
系数集为
\[
\mathcal H=\{0,1,v,v+1,v+3,v+6,\ldots,v+3(q-2)\},
\]
恰有 $N=q+2$ 个不同元素。此时
\[
\gamma=(q-1)v+1+\frac{3(q-2)(q-1)}2\equiv1-v\not\equiv0\pmod3.
\]
选择 $W$ 为所有 $\ell\le q+2,\ell\ne3$ 的素数之积。定义
\[
L=b+\tau,\qquad B=b+L=2b+\tau.
\]
两个 $E$ 为 $0,v$，故两根相隔的精度恰为 $L$，两个输出的分界恰为 $B$。

### 推论 5.1（完整双输出分布）

在本节的全素数配置中，固定精确事件的极限比例为
\[
\begin{array}{c|c}
(D_1,D_2)&\text{比例}\\\hline
(b,b)&1/2\\
(b+t,b+t),\ 1\le t<L&3^{-t}\\
(B,B)&1/(2\cdot3^L)\\
(B+j,B),\ j\ge1&3^{-(L+j)}\\
(B,B+j),\ j\ge1&3^{-(L+j)}
\end{array}
\tag{5.1}
\]
其余精确事件确定性不可能。特别地，两个输出分别无界，但不能同时大于 $B$；每个表中事件都有无穷多个全素数实现，形状不随 $j$ 改变。

**证明。** 两根同余到模 $3^L$，在模 $3^{L+1}$ 分开。单位参数不进入共同的模 $3$ 根类的比例为 $1/2$；在精度 $1\le t<L$ 停止的环层给出 $3^{-t}$。在共同的模 $3^L$ 类内，三个子类分别为第一根子类、第二根子类、都不是根的子类；最后一类给出 $(B,B)$ 的比例 $1/(2\cdot3^L)$。进入第一根的更深环层时，第二输出固定在 $B$，单根精确赋值给出 $3^{-(L+j)}$；另一侧相同。应用定理 4.1 转移到全素数计数。$\square$

### 六素数特例

取 $k=s=1,\tau=0$，则 $b=L=2$、$B=4$、$W=10$、$MW=90$。五个端点是
\[
p_0=n,\quad p_1=n+90d,\quad p_2=n+180d,\quad
p_3=n+270d,\quad p_5=n+450d.
\]
令
\[
D_1=F_3(p_0p_3p_5),\qquad D_2=F_3(p_1p_2p_5).
\]
在 $d,p_0,p_1,p_2,p_3,p_5$ 全为素数且 $F_3(n)=1$ 的集合里，全部单点 $F_3$ 为 $1$，全部二次单项式的 $F_3$ 为 $-1$。确定性有
\[
\min(D_1,D_2)\le4.
\]
对每个固定 $R\ge5$，$(D_1,D_2)=(R,4)$ 与 $(4,R)$ 各有无穷多个实现，比例各为 $3^{-(R-2)}$。基础计数规模为正常数乘以 $X^2/(\log X)^6$。

这一限制也有直接的整数证明：置 $x=90d$，则
\[
p_1p_2p_5-p_0p_3p_5=2x^2p_5.
\]
右边的三进赋值恰为 $4$，所以两个乘积加一不能同时被 $3^5$ 整除。

## 6. 指定有限的三进距离层级

### 定理 6.1

任取不同的非负整数 $z_1,\ldots,z_m$，令 $Z=\max_i z_i$。在第 1 节取
\[
u_i=3z_i,\quad S=6Z+1,\quad r_j=3(2Z+j)\quad(1\le j\le q-2).
\]
这些系数全部互异，且 $\gamma\equiv1\pmod3$。得到的根距离为
\[
\boxed{L_{ij}=b+1+v_3(z_i-z_j).}
\tag{6.1}
\]
取满足第 4 节条件的 $W$ 后，定理 3.1 的完整联合尾律在该全素数配置中成立为极限比例。因而给定整数列表的三进接近关系，经过统一增加 $b+1$ 层后，精确出现在共享步长的乘积根中。

**证明。** 所有 $u_i$ 位于 $[0,3Z]$，所有 $S-u_i$ 位于 $[3Z+1,6Z+1]$，而全部 $r_j>S$。同一组内也互不相同。$\gamma\equiv S\equiv1\pmod3$。另有
\[
E_i-E_j=(u_i-u_j)(S-u_i-u_j),
\]
第二因子模 $3$ 为 $1$，所以 $v_3(E_i-E_j)=1+v_3(z_i-z_j)$。使用定理 2.1 和定理 4.1。$\square$

例如取 $k=s=1$、$(z_1,z_2,z_3)=(0,1,4)$。系数集为
\[
\mathcal H=\{0,3,12,13,22,25,27\},\qquad MW=9\cdot70=630.
\]
三个输出分别取端点系数组 $\{0,25,27\}$、$\{3,22,27\}$、$\{12,13,27\}$。根距离为 $L_{12}=L_{13}=3,L_{23}=4$。因此，对每个固定 $R\ge7$，
\[
(D_1,D_2,D_3)=(5,6,R)
\]
有无穷多个八素数实现；相应条件比例为 $3^{-(R-2)}$。第二、三输出能共同达到 $6$，却不能共同达到 $7$；第一输出与任一另外输出则不能共同达到 $6$。

## 7. 范围与依赖

全部低次数数据固定、每个输出各自可任意升层，都不蕴含多个输出能独立指定。这里给出的是共享单位参数到若干根的距离过程，根间距决定完整的有限阈值律。单根与球交集的计数属于经典三进几何，素数存在性来自 (LF)。

所有形状、形式数及阈值固定；不从逐固定阈值的极限推出随 $X$ 增长的深度范围或无界矩的极限。实际间距为固定系数乘以可变素数 $d$；固定 $d$ 后的一变量系统不满足本文件使用的有限复杂度条件。这些结果不包含固定孪生间距的存在性结论。

## 参考

[1] B. Green and T. Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850, Main Theorem and Corollary 1.7.
https://annals.math.princeton.edu/2010/171-3/p08

[2] B. Green and T. Tao, *The Möbius function is strongly orthogonal to nilsequences*, Annals of Mathematics 175 (2012), 541–566.
https://annals.math.princeton.edu/2012/175-2/p03

[3] B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm*, Annals of Mathematics 176 (2012), 1231–1372; corrected preprint arXiv:1009.3998v5 and the authors' erratum.
https://arxiv.org/abs/1009.3998v5

[4] D. Snyder, *Products of p-Adic Valuation Trees*, arXiv:2308.11718. 多项式根及赋值树的背景参考；不以此文代替本文的联合计数证明。
https://arxiv.org/abs/2308.11718

# 素数伸缩配置上的 F₃ 联合深度律

对整数 $u>1$ 定义
\[
F_3(u)=v_3(u+1)-v_3(u-1).
\]
赋值只作用于非零整数。所有极限中的整数参数 $k,R$ 均先固定，再令实数 $X\to\infty$。本文的素数计数使用有限复杂度线性形式素数定理作为外部输入。

## 1. 配置与计数

固定 $k\ge1$，令
\[
h_0=0,\qquad
h_1=2+4\cdot3^{2k},\quad
h_2=2+10\cdot3^{2k},\quad
h_3=2+16\cdot3^{2k}.
\]
对正整数 $n,d$，置 $p_i=n+h_i d$，并定义
\[
D_i(n,d)=F_3(p_0p_i),\qquad i=1,2,3.
\]
令 $\mathcal P_k(X)$ 为满足下列条件的参数对集合：
\[
X<n,d\le2X,\qquad
 d,p_0,p_1,p_2,p_3\text{ 均为素数},
\]
\[
F_3(n)=k,\qquad d\equiv1\pmod{3^{2k+1}}.
\]
记 $B_k(X)=|\mathcal P_k(X)|$。对 $i\in\{1,2,3\}$、$R\ge2k+2$，记 $N_{k,i,R}(X)$ 为其中满足
\[
D_i=R,\qquad D_j=2k+1\quad(j\ne i)
\]
的参数对数。

## 2. 线性形式素数定理

使用以下已知定理的二维特例 [1–3]：设 $\psi_1,\ldots,\psi_s$ 是固定的非恒定整数仿射线性形式，其线性部分两两不成比例。在边长与 $X$ 同阶的凸矩形 $K_X$ 上，假设所有 $\psi_i$ 均为正且与 $X$ 同阶。定义
\[
\beta_\ell=\frac1{\ell^2}
\sum_{\mathbf a\bmod\ell}
\prod_{i=1}^{s}\frac{\ell}{\ell-1}
\mathbf1_{\ell\nmid\psi_i(\mathbf a)}.
\]
则
\[
\#\{\mathbf x\in K_X\cap\mathbb Z^2:
\psi_1(\mathbf x),\ldots,\psi_s(\mathbf x)\text{ 均为素数}\}
=\left(\prod_\ell\beta_\ell+o(1)\right)
\frac{\operatorname{area}(K_X)}{(\log X)^s}.
\tag{LF}
\]
有限复杂度保证 $\beta_\ell=1+O(\ell^{-2})$，除有限个素数外统一成立。若每个局部因子为正，乘积严格为正。

[1] 的 Main Theorem 原以 $\mathrm{GI}(s)$、$\mathrm{MN}(s)$ 为输入；[2–3] 已给出所需结果，故这里使用的是无条件定理。[1, Corollary 1.7] 本身已经无条件覆盖复杂度至多 $2$ 的情况。本文包含 $d$ 在内的五个形式复杂度至多 $3$；不要求 $d$ 为素数时的四形式版本只需复杂度 $2$。

从 von Mangoldt 加权版本到 (LF)，可以直接排除高次素数幂：任一个非恒定形式取高次素数幂的参数点数为 $O(X^{3/2}\log X)$，其对加权和的贡献为 $o(X^2)$。在剩余点上，每个对数权均为 $\log X+O(1)$。

### 引理 2.1（固定三进剩余类）

设 $A\ge1$、$M=3^A$，并固定代表 $0\le a_0,b_0<M$ 满足
\[
a_0\equiv-1\pmod3,\qquad b_0\equiv1\pmod3.
\]
令 $H_k=\{h_0,h_1,h_2,h_3\}$、
\[
\nu_\ell(k)=|\{h\bmod\ell:h\in H_k\}|,
\qquad
\mathfrak S_k=\left(\frac32\right)^5
\prod_{\ell\ne3}
\frac{\ell^3(\ell-\nu_\ell(k))}{(\ell-1)^4}.
\]
则 $\mathfrak S_k>0$。令 $A_{a_0,b_0;M}(X)$ 计数满足
\[
X<n,d\le2X,\quad(n,d)\equiv(a_0,b_0)\pmod M,
\quad d,n,n+h_1d,n+h_2d,n+h_3d\text{ 均为素数}
\]
的参数对，则
\[
A_{a_0,b_0;M}(X)
=\left(\frac{\mathfrak S_k}{M^2}+o_{k,M}(1)\right)
\frac{X^2}{(\log X)^5}.
\tag{2.1}
\]
该主项不依赖于所选 $a_0,b_0$。

**证明。** 代入 $n=a_0+Mx,d=b_0+My$。五个线性部分为
\[
(0,M),\quad(M,0),\quad(M,Mh_1),\quad(M,Mh_2),\quad(M,Mh_3).
\]
它们两两不成比例。将每个形式以外的四个形式各自分为单元素类，可见复杂度至多 $3$。参数矩形面积为 $X^2/M^2$，所有形式在其中正且与 $X$ 同阶。

在素数 $3$ 处，五个形式均为单位，故局部因子为 $(3/2)^5$。在 $\ell\ne3$ 处，参数变换在模 $\ell$ 上可逆。要求 $d\ne0$ 后，共有 $\ell-1$ 种 $d$，每种 $d$ 对应的 $n/d$ 必避开 $\nu_\ell(k)$ 个剩余类。因此合格点数为
\[
(\ell-1)(\ell-\nu_\ell(k)),
\]
局部因子即为公式中所列值。所有 $h_i$ 均为偶数，所以 $\nu_2(k)=1<2$；对 $\ell\ge5$，有 $\nu_\ell(k)\le4<\ell$。局部因子全部为正。

除整除某个非零 $h_i-h_j$ 的有限个素数外，$\nu_\ell(k)=4$，从而因子为
\[
\frac{\ell^3(\ell-4)}{(\ell-1)^4}
=1-\frac{6\ell^2-4\ell+1}{(\ell-1)^4}
=1+O(\ell^{-2}).
\]
乘积绝对收敛到正数。应用 (LF) 即得。$\square$

## 3. 三路升层的确定性结构

### 引理 3.1

若 $n>1$、$d>0$ 满足 $F_3(n)=k$、$d\equiv1\pmod{3^{2k+1}}$，则
\[
(F_3(p_0),F_3(p_1),F_3(p_2),F_3(p_3))=(k,-k,-k,-k).
\]
三个 $D_i$ 均至少为 $2k+1$，其中恰好一个至少为 $2k+2$，其余两个恰为 $2k+1$。

**证明。** 写 $n=-1+3^ka$，$3\nmid a$。因为
\[
h_i d-2=3^{2k}c_i(d),\qquad c_i(d)\equiv1\pmod3,
\]
有 $p_i-1=3^ka+(h_i d-2)$，其赋值恰为 $k$，且 $p_i\equiv1\pmod3$。故四个单点值如述。

置 $Q_i=n(n+h_i d)+1$。直接展开得到
\[
Q_i=3^{2k}f_{i,d}(a),\qquad
f_{i,d}(a)=a^2+3^kc_i(d)a-c_i(d).
\tag{3.1}
\]
括号模 $3$ 为 $a^2-1=0$。又 $p_0p_i\equiv-1\pmod3$，所以 $D_i=v_3(Q_i)\ge2k+1$。

两次相邻差均满足
\[
Q_{i+1}-Q_i=6\cdot3^{2k}nd
=2\cdot3^{2k+1}nd.
\]
三个商 $Q_i/3^{2k+1}$ 模 $3$ 依次相差非零数 $2nd$，故恰有一个被 $3$ 整除。$\square$

### 引理 3.2（精确有限层计数）

固定 $i$ 和 $u\ge0$。在模足够高的 $3^A$ 下，对满足引理 3.1 基础同余条件的 $(n,d)$ 等权计数，有
\[
\frac{\#\{D_i\ge2k+1+u\}}{\#\{F_3(n)=k,\ d\equiv1\ (3^{2k+1})\}}
=3^{-u}.
\tag{3.2}
\]
因此，对 $R\ge2k+2$，精确事件
\[
D_i=R,\qquad D_j=2k+1\ (j\ne i)
\]
所占比例为 $2/3^{R-2k}$。例如可统一取 $A\ge R+1$ 来判定此精确事件。

**证明。** 固定 $d$ 的剩余类。对三进单位 $a$，多项式 $f_{i,d}(a)$ 模 $3$ 的根恰为 $a=1,2$，且
\[
f'_{i,d}(a)=2a+3^kc_i(d)\not\equiv0\pmod3.
\]
每个根向下一个三进精度恰有一次提升：若 $f(a)\equiv0\pmod{3^v}$，则
\[
f(a+3^v b)\equiv f(a)+3^vbf'(a)\pmod{3^{v+1}},
\]
在 $b\bmod3$ 中恰有一个解。所以模 $3^{u+1}$ 恰有两个根，而单位类共有 $2\cdot3^u$ 个。式 (3.1) 给出 (3.2)。该比例对每个允许的 $d$ 都相同，故对 $d$ 求和仍然成立。

相邻门槛相减给出
\[
3^{-(R-2k-1)}-3^{-(R-2k)}=2/3^{R-2k}.
\]
其余两路的精确值由引理 3.1 决定。所有条件在所列固定精度上已确定。$\square$

## 4. 全素数配置的计数与联合律

定义正数
\[
\kappa_k=\frac{3^{3-3k}}{16}
\prod_{\ell\ne3}\frac{\ell^3(\ell-\nu_\ell(k))}{(\ell-1)^4}.
\]

### 定理 4.1

对每个固定 $k\ge1$，有
\[
B_k(X)=(\kappa_k+o_k(1))\frac{X^2}{(\log X)^5}.
\tag{4.1}
\]
对每个固定 $i\in\{1,2,3\}$ 和 $R\ge2k+2$，有
\[
N_{k,i,R}(X)
=\left(\frac{2\kappa_k}{3^{R-2k}}+o_{k,R}(1)\right)
\frac{X^2}{(\log X)^5}.
\tag{4.2}
\]
因此，在 $\mathcal P_k(X)$ 上等权抽取 $(n,d)$，有
\[
\Pr(D_i=R,\ D_j=2k+1\ (j\ne i))
\longrightarrow\frac2{3^{R-2k}}.
\tag{4.3}
\]

**证明。** 取固定 $A\ge2k+1$、$M=3^A$。基础条件在模 $M$ 上的单点类数和步长类数分别为
\[
2\cdot3^{A-k-1},\qquad3^{A-2k-1},
\]
故参数类总数为 $2\cdot3^{2A-3k-2}$。每类均满足引理 2.1 的单位条件，且获得完全相同的素数计数主项。因此总系数为
\[
\frac{2}{3^{3k+2}}\mathfrak S_k=\kappa_k,
\]
得到 (4.1)。

进一步取 $A\ge R+1$，由引理 3.2，目标事件恰占基础参数类的 $2/3^{R-2k}$。引理 2.1 对有限个类逐项求和，得到 (4.2)。最后除以严格正的 (4.1) 即得 (4.3)。这里没有将双端或多端素性假设为相互独立；每个参数类的真实素数主项均来自 (LF)。$\square$

### 推论 4.2（任意精确升层的素数实现）

对每个 $k\ge1$、$R\ge2k+2$ 和 $i\in\{1,2,3\}$，存在无穷多个正整数参数对 $(n,d)$，使 $d,p_0,p_1,p_2,p_3$ 全为素数，并且
\[
(F_3(p_0),F_3(p_1),F_3(p_2),F_3(p_3))=(k,-k,-k,-k),
\]
\[
D_i=R,\qquad D_j=2k+1\quad(j\ne i).
\]

**证明。** 式 (4.2) 的主系数严格为正，且 $X^2/(\log X)^5\to\infty$。取互不相交且趋于无穷的参数盒即可。$\square$

### 推论 4.3（最大深度）

对每个固定 $R\ge2k+2$，
\[
\Pr_{\mathcal P_k(X)}\bigl(\max_iD_i=R\bigr)
\longrightarrow\frac2{3^{R-2k-1}}.
\]
三个升层位置各自的极限概率为 $1/3$。

**证明。** 三个精确事件互斥，使用 (4.3) 相加。位置事件等价于 $D_i\ge2k+2$，其有限类比例由引理 3.2 直接等于 $1/3$，再用引理 2.1；不需要交换无限级数与极限。$\square$

## 5. 四个固定系数的具体推论

当 $k=1$，偏移系数为 $38,92,146$。存在无穷多个 $(n,d)$，使
\[
d,n,n+38d,n+92d,n+146d\text{ 全为素数},
\]
\[
(F_3(n),F_3(n+38d),F_3(n+92d),F_3(n+146d))=(1,-1,-1,-1),
\]
\[
(F_3(n(n+38d)),F_3(n(n+92d)),F_3(n(n+146d)))=(3,5,3).
\]
还可附加 $(n,d)\equiv(5,1)\pmod{729}$。

**证明。** 对种子 $(n,d)=(5,1)$，四个单点值如述，而三个乘积加一依次为
\[
5\cdot43+1=216=8\cdot3^3,\quad
5\cdot97+1=486=2\cdot3^5,\quad
5\cdot151+1=756=28\cdot3^3.
\]
同余到模 $3^6$ 保留这些有限赋值及全部单点值。引理 2.1 对类 $(5,1)\pmod{729}$ 给出严格正的五素数主项。种子中的 $d=1$ 不需要为素数；被计数的实际参数 $d$ 由 (LF) 要求为素数。$\square$

## 6. 范围

以上结果允许 $n,d$ 同时变化，并在计数时将二者都限制在 $(X,2X]$；实际间距为 $h_i d$，不固定。将 $d$ 固定后，形式 $n+h_i d$ 的线性部分成比例，不能再使用 (LF)。这些结论没有证明固定间距的素数对无穷性。

极限中的 $k,R$ 是固定参数。上述定理没有给出允许 $k$ 或 $R$ 随 $X$ 增长的统一误差，也没有给出可计算的统一起点。这里的正下界是所述伸缩族的真实素数下界，不是平衡逆元盒中三素数计数或固定孪生间距的下界。

## 参考

[1] B. Green and T. Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850. Main Theorem, Lemma 1.6, Corollary 1.7；素数计数版本及局部因子见 §1。
https://annals.math.princeton.edu/2010/171-3/p08
https://arxiv.org/abs/math/0606088v2

[2] B. Green and T. Tao, *The Möbius function is strongly orthogonal to nilsequences*, Annals of Mathematics 175 (2012), 541–566. 提供所有阶数的 $\mathrm{MN}(s)$。
https://annals.math.princeton.edu/2012/175-2/p03

[3] B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers $U^{s+1}[N]$-norm*, Annals of Mathematics 176 (2012), 1231–1372. Theorem 1.3 及其后的有限复杂度素数应用。这里核对的预印本为 2026-04-23 修订的 v5。
https://arxiv.org/abs/1009.3998v5

本文的联合律由有限三进计数与上述已知素数定理结合得到；不把 (LF) 当作新证明的定理。书面证明不等同于 Lean 内核形式化。

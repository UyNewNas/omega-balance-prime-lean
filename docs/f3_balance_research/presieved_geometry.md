# 逆元层的预筛分布

设 $j,c\ge1$，$r=2j+c$，$t=3^j$、$s=3^c$、$m=t^2s$，固定 $\epsilon\in\{\pm1\}$。研究有序奇数对
\[
1<a,b<m,\quad ab\equiv1\pmod m,\quad F_3(a)=F_3(b)=-\epsilon j.
\]
固定矩形 $R=(\alpha,\beta]\times(\gamma,\delta]\subset[0,1]^2$，面积为 $\mathcal A>0$。记
\[
\ell_R(z)=[\min(\beta,z-\gamma)-\max(\alpha,z-\delta)]_+.
\]
该函数总变差有绝对上界，且 $\int\ell_R=\mathcal A$。

本文使用 [平衡逆元对的层级几何](inverse_geometry.md) 定理 2.1 的参数化：可行的 $h$ 满足 $1\le h<s$、$h\equiv-\epsilon\pmod3$；每条线
\[
a+b=C_h:=2\epsilon+2t^2h
\]
有两个根分支，每个分支以 $2ts$ 为步长。其盒内参数是连续整数区间，长度为
\[
L_{h,u_0}=\frac t2\ell_R(C_h/m)+O(1).
\]

## 1. 带平方自由整除条件的分布

对素数 $\ell\ge5$，令
\[
\rho_\ell(C)=3-\mathbf1_{\ell\mid C}+\left(\frac{C^2-8}{\ell}\right).
\]
这是 $\ell\mid a(C-a)(a(C-a)-2)$ 的根数；参见上述几何文件命题 5.1。对与 $6$ 互素的平方自由 $d$，定义
\[
\rho_h(d)=\prod_{\ell\mid d}\rho_\ell(C_h),\quad g_h(d)=\rho_h(d)/d,
\quad g(d)=\prod_{\ell\mid d}\left(\frac3\ell-\frac2{\ell^2}\right).
\]
记 $A_d$ 为本层盒中另满足 $d\mid ab(ab-2)$ 的点数，$X_j=ts\mathcal A/6$。

### 定理 1.1

统一于 $j,c,d$ 及盒子，
\[
A_d=g(d)X_j+O\bigl((t+s)4^{\omega(d)}\bigr).
\]

**证明。** 每个根分支的步长与 $d$ 互素，故其中满足整除条件的参数恰属于 $\rho_h(d)$ 个模 $d$ 类。两个分支相加得到
\[
A_{d,h}=t\ell_R(C_h/m)g_h(d)+O(\rho_h(d)).
\]
全部分支的舍入误差为 $O(s4^{\omega(d)})$。

将 $h$ 按公差 $3$ 排列，$C_h$ 的公差为 $6t^2$，与 $d$ 互素。因此 $g_h(d)$ 以 $d$ 为周期，且完整周期的平均为 $g(d)$。模 $\ell$ 下全部坏点 $(a,b)$ 有 $3\ell-2$ 个，中国剩余定理给出这个平均式。

由于 $g_h(d)\ge0$，任意不完整周期的中心化部分和绝对值不超过
\[
dg(d)=\prod_{\ell\mid d}(3-2/\ell)\le3^{\omega(d)}.
\]
对有界变差权 $\ell_R(2h/s)$ 使用离散分部求和，再用步长 $6/s$ 的 Riemann 和，得到
\[
\sum_h\ell_R(2h/s)g_h(d)=g(d)\frac s6\mathcal A+O(3^{\omega(d)}).
\]
把 $2h/s$ 改为 $C_h/m$ 的总误差乘以 $t$ 后为 $O(ts/m)$，故可吸收。相加两类误差即得。$\square$

### 推论 1.2

允许大小不超过 $3^{\omega(d)}$ 的权时，
\[
\sum_{d\le D}^{*}3^{\omega(d)}|A_d-g(d)X_j|
\ll(t+s)D(1+\log D)^{11}.
\]
没有该额外权时，可将对数指数改为 $3$。星号表示平方自由且与 $6$ 互素。

**证明。** 使用 $12^{\omega(d)}\le\tau_{12}(d)$ 及
$\sum_{d\le D}\tau_k(d)\ll D(1+\log D)^{k-1}$；无额外权时用 $k=4$。$\square$

## 2. 筛法基本引理

采用以下经典形式 [1, Lemma 17 and Corollary 19；2, Theorem 12.2]。设非负有限序列的整除计数为 $X_0g(d)+r_d$，局部函数满足 $0\le g(\ell)<1$，且存在固定 $\kappa,K$，使
\[
\prod_{w\le\ell\le y}(1-g(\ell))^{-1}
\le K\left(\frac{\log y}{\log w}\right)^\kappa.
\]
当 $D=y^\nu$、$\nu$ 足够大时，存在绝对值不超过 $1$、支撑于平方自由 $d\le D$ 的上下筛权，给出
\[
S(y)=X_0V(y)(1+O_{\kappa,K}(e^{-\nu}))
+O\left(\sum_{d\le D}^{*}|r_d|\right),
\quad V(y)=\prod_{\ell\le y}(1-g(\ell)).
\tag{FL}
\]
所有乘积和求和只涉及指定的筛素数。

对单条线，$\rho_\ell(C)/\ell\le4/\ell$ 给出与 $C$ 无关的维数 $4$ 上包络。由 Mertens 乘积及 $\sum\ell^{-2}<\infty$，统一有
\[
V_C(y):=\prod_{5\le\ell\le y}(1-\rho_\ell(C)/\ell)
\gg(\log y)^{-4}.
\tag{2.1}
\]
对平均局部函数 $g(\ell)=3/\ell-2/\ell^2$，相应维数为 $3$，并有
\[
V(y):=\prod_{5\le\ell\le y}(1-3/\ell+2/\ell^2)
\asymp(\log y)^{-3}.
\tag{2.2}
\]
素数 $2,3$ 不整除本层任何 $ab(ab-2)$，故不列入筛素数。

## 3. 保留斜线相位的预筛主项

令 $N_y(R)$ 计数本层盒中另满足 $P^-(ab(ab-2))>y$ 的点，其中 $P^-$ 表示最小素因子。定义
\[
M_y(R)=t\sum_{\substack{1\le h<s\\h\equiv-\epsilon\ (3)}}
\ell_R(C_h/m)V_{C_h}(y).
\]

### 定理 3.1

对 $D\ge y\ge5$、$\nu=\log D/\log y$ 足够大，有
\[
N_y(R)=M_y(R)+O\left(e^{-\nu}M_y(R)+sD(1+\log D)^3\right).
\]

**证明。** 固定一个根分支，其参数区间长度为 $L_{h,u_0}$。中国剩余定理给出整除计数
\[
L_{h,u_0}g_h(d)+O(\rho_h(d)).
\]
应用 (FL)，并用 $\rho_h(d)\le4^{\omega(d)}$，该分支余项为 $O(D(1+\log D)^3)$。共有 $2s/3$ 个分支。将 $L_{h,u_0}$ 换成弦长主项时的 $O(s)$ 舍入误差也被总余项吸收。各分支的维数上包络相同，故常数统一。$\square$

### 推论 3.2（固定临界距离）

固定 $c\ge1$，令 $j\to\infty$，取 $y=\exp\sqrt{\log m}$。若
\[
\sum_{h\equiv-\epsilon\ (3)}\ell_R(2h/s)>0,
\]
则
\[
N_y(R)=(1+o(1))M_y(R).
\]

**证明。** 取 $D=\lfloor t^{1/2}\rfloor$，则 $\nu\to\infty$。由 (2.1) 及正弦长假设，$M_y(R)\gg_{R,c}t/(\log m)^2$。加性误差 $s\sqrt t\log^3t$ 相对该量趋零。$\square$

当 $M_y=0$ 时，只使用定理 3.1 的加性形式，不作相对渐近断言。

### 推论 3.3（单侧盒）

令 $c=2$、$R=(1/4,1/3]\times(1/2,2/3]$。置 $C_j=-2+8\cdot9^j$、$y_j=\exp\sqrt{(2j+2)\log3}$。则
\[
N^{\mathrm{rough}}_{+j}(R)=(1+o(1))\frac{3^j}{12}V_{C_j}(y_j),
\qquad N^{\mathrm{rough}}_{-j}(R)=0.
\]

**证明。** [逆元几何](inverse_geometry.md) 定理 4.2 表明只有正层 $h=4$ 的线进入盒子，其弦长为 $1/12$；负层本身为空。应用推论 3.2。$\square$

## 4. 面积型主项的两个范围

### 定理 4.1（近临界范围）

令 $r\to\infty$、$r=2j+c$、$1\le c\le j$，且 $c/\sqrt r\to\infty$。在 $y=\exp\sqrt{\log m}$ 下，对固定正面积矩形及任一符号，
\[
N_y(R)=(1+o(1))\frac{ts}{6}\mathcal A V(y).
\]

**证明。** 取 $D=\lfloor s^{1/2}\rfloor$。定理 1.1 及 (FL) 给出主项相对误差 $O(e^{-\nu})$ 和加性误差 $O(tD(1+\log D)^3)$。这里
\[
\nu\asymp c/\sqrt r\to\infty,
\quad V(y)\asymp(\log m)^{-3/2}.
\]
归一化后的加性误差至多
\[
O_R\left(s^{-1/2}(1+\log s)^3(\log m)^{3/2}\right)=o(1).
\]
故结论成立。$\square$

### 定理 4.2（固定指数余量）

取固定平衡矩形 $R=(1/4,1/3]\times(1/2,2/3]$。对任意固定 $\varepsilon\in(0,1/2)$，统一于 $3^{j+1}\le m^{1/2-\varepsilon}$ 及两个符号，仍有
\[
N_y(R)=(1+o_\varepsilon(1))\frac{m\mathcal A}{6\cdot3^j}V(y),
\qquad y=\exp\sqrt{\log m}.
\]

**证明。** 对精确符号层，取同侧深度至少 $j$ 与至少 $j+1$ 的计数之差。[模双曲线筛](sieve_bounds.md) 定理 2.1 的逐侧证明给出
\[
A_{d,j,\epsilon}=g(d)X_j+O_\eta(m^{1/2+\eta}d^{1/2+\eta}),
\quad X_j=\frac{m\mathcal A}{6\cdot3^j}+O(1).
\]
取 $D=m^\delta$，其中固定 $\delta,\eta>0$ 满足 $\eta+3\delta/2<\varepsilon$。累计余项为 $O(m^{1/2+\eta+3\delta/2+o(1)})$，相对 $X_jV(y)\gg_R m^{1/2+\varepsilon}(\log m)^{-3/2}$ 趋零。同时 $\nu=\log D/\log y\to\infty$，应用 (FL)。$\square$

两条定理的主项属于预筛集合，不要求 $a,b,ab-2$ 为素数。

## 5. 有界几乎素数的正下界

### 定理 5.1

在推论 3.3 的正层盒中，存在绝对整数 $K_0$，使每个充分大的 $j$ 都有
\[
\gg\frac{3^j}{j^4}
\]
个有序数对满足
\[
\Omega(a)+\Omega(b)+\Omega(ab-2)\le K_0.
\]

**证明。** 置 $t=3^j$，取 $D=t^{1/2}$、$y=t^\delta$，其中固定 $\delta>0$ 足够小，使 (FL) 的相对误差小于 $1/2$。此时 $\nu=1/(2\delta)$。由 (2.1) 及定理 3.1，预筛数对数至少为常数倍 $t/(\log t)^4$；加性误差 $O(\sqrt t\log^3t)$ 为低阶。

每个这样的点满足 $a,b<9t^2$、$ab-2<81t^4$，而三个数的全部素因子大于 $t^\delta$。故
\[
\Omega(a)+\Omega(b)+\Omega(ab-2)
<\frac{8\log t+\log6561}{\delta\log t}.
\]
取固定整数 $K_0>9/\delta$，对充分大的 $t$ 即得。$\square$

## 6. 固定有限筛的相位

固定有限素数集合 $\mathcal P\subset\{5,7,11,\ldots\}$。由逐分支中国剩余定理，固定 $c$ 时有
\[
N^{\mathcal P}_{j,c,\epsilon}(R)
=t\sum_h\ell_R(2h/s)\prod_{\ell\in\mathcal P}(1-\rho_\ell(C_h)/\ell)+O_\mathcal P(s).
\]
在推论 3.3 的单线盒中，取 $\mathcal P=\{5,7,11\}$。$9$ 在这三个模数中的阶分别为 $2,3,5$，故局部乘积关于 $j$ 有周期 $30$。直接代入根数公式得到
\[
\prod_{\ell\in\mathcal P}(1-\rho_\ell(C_j)/\ell)
=\begin{cases}12/55,&j\equiv12\pmod{30},\\216/385,&j\equiv25\pmod{30}.
\end{cases}
\]
因此沿两条子序列，有限预筛计数与原始层计数之比分别趋向这两个不同的数。

## 参考

[1] T. Tao, *254A, Notes 4: Some sieve theory* (2015), Lemma 17 and Corollary 19：
https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/

[2] K. S. Kedlaya, *Notes on analytic number theory*, Chapter 12, Theorem 12.2：
https://kskedlaya.org/ant/chap-brun.html

Mertens 乘积及筛法基本引理在本文作为外部定理使用；几何分支和有限整除计数分别在本文及所链接的证明中给出。

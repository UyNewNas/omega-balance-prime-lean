# 带 F₃ 深度限制的模双曲线筛

设 $m=3^r$、$z=\lfloor m^{2/3}\rfloor$。对 $1\le J\le r$，令 $C_{r,\ge J}$ 计数
\[
z<a<b,\quad ab<m^2,\quad ab\equiv1\pmod{2m},
\quad a,b,ab-2\text{ 均为素数},\quad |F_3(a)|\ge J.
\]
$\omega(d)$ 表示不同素因子个数，$\Omega(d)$ 表示计重个数。以下筛模数 $d$ 均平方自由且与 $6$ 互素。置 $t=3^J$，则奇数单位上的深度条件等价于 $a\equiv\pm1\pmod t$。

## 1. 完全指数和与区间完成

使用经典 Kloosterman–Weil 上界：对每个固定 $\eta>0$，
\[
\left|\sum_{x\bmod M}^{*}e_M(ux+vx^{-1})\right|
\ll_\eta M^{1/2+\eta}\sqrt{\gcd(v,M)},\qquad v\not\equiv0\pmod M.
\tag{KW}
\]
这里可由 $\tau(M)\sqrt{M\gcd(u,v,M)}$ 型上界放宽得到。出处见文末 [1]。

对 $t\mid M$ 的一个单位类 $x\equiv c\pmod t$，以
\[
\mathbf1_{x\equiv c\ (t)}=\frac1t\sum_{b\bmod t}e_t(b(x-c))
\]
展开，所得完全和仍满足 (KW)，因为第二个系数 $v$ 不变且所取的是归一化平均。

对一个长度至多 $M$ 的区间，以有限 Fourier 展开完成，其系数的 $\ell^1$ 范数为 $O(M\log(2M))$，故相应不完全逆元和为
\[
O_\eta\bigl(M^{1/2+\eta}\sqrt{\gcd(v,M)}\log(2M)\bigr).
\tag{1.1}
\]
对另一整数区间的非零频率系数 $F(k)$，完整周期不贡献，且
\[
|F(k)|\ll\frac{M}{\min(k,M-k)},\qquad0<k<M.
\]
按 $g=\gcd(k,M)$ 分组，有
\[
\frac1M\sum_{k=1}^{M-1}|F(k)|\sqrt{\gcd(k,M)}
\ll\log(2M)\sum_{g\mid M}g^{-1/2}\ll_\eta M^\eta.
\tag{1.2}
\]
所有固定个数的对数及任意小指数余量可通过缩小初始 $\eta$ 吸收。

## 2. 合并同余后的矩形计数

取整数端点区间 $I=(U,U+A]$、$J_b=(V,V+B]$，满足
\[
1\le A\le m,\qquad1\le B\le4m^{4/3}.
\]
令 $A_d$ 计数其中的奇数对，满足 $ab\equiv1\pmod m$、$a\equiv\pm1\pmod t$ 及 $d\mid ab(ab-2)$。

### 定理 2.1

令
\[
g(d)=\prod_{\ell\mid d}\left(\frac3\ell-\frac2{\ell^2}\right),\qquad X_0=\frac{AB}{2mt}.
\]
对每个固定 $\eta>0$，统一于上述参数，
\[
A_d=g(d)X_0+O_\eta\left(m^{1/2+\eta}d^{1/2+\eta}\right).
\tag{2.1}
\]

**证明。** 对每个 $\ell\ge5$，有点态恒等式
\[
\mathbf1_{\ell\mid ab(ab-2)}
=\mathbf1_{\ell\mid a}+\mathbf1_{\ell\mid b}
-\mathbf1_{\ell\mid a,\ell\mid b}+\mathbf1_{ab\equiv2\ (\ell)}.
\]
乘开后，将 $d$ 的素因子分给两两互素的 $d_1,d_2,d_3,d_4$，乘积为 $d$。相应项符号为 $\mu(d_3)$，且满足
\[
d_1d_3\mid a,\quad d_2d_3\mid b,\quad ab\equiv2\pmod{d_4}.
\]
置 $D_a=d_1d_3,D_b=d_2d_3$，$a=D_ax,b=D_by$。模 $m$ 和模 $d_4$ 的条件合成为
\[
xy\equiv c\pmod M,\qquad M=md_4,
\]
其中 $c$ 是单位，模 $m$ 同余于 $(D_aD_b)^{-1}$，模 $d_4$ 同余于 $2(D_aD_b)^{-1}$。另有 $x,y$ 为奇数，$x\equiv\pm D_a^{-1}\pmod t$。

先取一个符号。置缩放实长度 $X=A/D_a,Y=B/D_b$，把 $y$ 写为 $1+2v$。对模 $M$ 的条件作加性 Fourier 展开。零频的两个计数为
\[
N_x=\frac{X\varphi(d_4)}{2td_4}+O(2^{\omega(d_4)}),\qquad
N_y=Y/2+O(1).
\]
第一个等式由对 $d_4$ 的容斥和中国剩余定理给出；模 $t$ 的单位条件已排除因子 $3$。零频主项为 $AB\varphi(d_4)/(4mtD_aD_b d_4^2)$，舍入误差至多
\[
O\left(2^{\omega(d_4)}Y/M+X/M+2^{\omega(d_4)}/M\right).
\]
由 $B\le4m^{4/3}$，此误差被 $O_\eta(M^{1/2+\eta})$ 吸收。非零频由 (1.1)–(1.2) 同样给出 $O_\eta(M^{1/2+\eta})$。

相加两个符号，这个合并分量的计数为
\[
\frac{AB}{2mtD_aD_b}\frac{\varphi(d_4)}{d_4^2}
+O_\eta((md_4)^{1/2+\eta}).
\]
对四项分配求和，每个素数对主项的局部因子为
\[
\frac1\ell+\frac1\ell-\frac1{\ell^2}+\frac{\ell-1}{\ell^2}
=\frac3\ell-\frac2{\ell^2}.
\]
分量数至多 $4^{\omega(d)}\ll_\eta d^\eta$。重新分配指数余量，得到 (2.1)。$\square$

### 推论 2.2

若 $r_d=A_d-g(d)X_0$，则
\[
\sum_{d\le D}^{*}3^{\omega(d)}|r_d|
\ll_\eta m^{1/2+\eta}D^{3/2+\eta}.
\tag{2.2}
\]
星号表示平方自由且与 $6$ 互素。对于固定 $t$、$AB\asymp m^2$，$D\le m^{1/3-\varepsilon}$ 时有幂次余量；若 $t\le m^\gamma$，相应充分范围为 $D\le m^{(1-2\gamma)/3-\varepsilon}$。

## 3. Selberg 上界筛

对 $\ell\ge5$，模 $\ell$ 中使 $\ell\mid ab(ab-2)$ 的点数为 $3\ell-2$：$a=0$ 或 $b=0$ 共 $2\ell-1$ 个，$ab=2$ 另有 $\ell-1$ 个。于是
\[
1-g(\ell)=(1-1/\ell)(1-2/\ell).
\]
定义
\[
C_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right),\qquad
h(\ell)=\frac{g(\ell)}{1-g(\ell)}.
\]
经典乘法函数均值公式 [2, Chapter 14] 给出
\[
G(Z):=\sum_{\substack{d\le Z\\(d,6)=1}}\mu^2(d)\prod_{\ell\mid d}h(\ell)
\sim\frac{(\log Z)^3}{216C_2}.
\tag{3.1}
\]
常数的核对如下。设 $g(2)=g(3)=0$，则
\[
\prod_\ell(1-g(\ell))(1-1/\ell)^{-3}=36C_2.
\]
其倒数乘以 $1/\Gamma(4)=1/6$，得到 (3.1) 的系数。

Selberg 最优平方权 [2, Chapter 13] 可取 $\rho_1=1$、$|\rho_d|\le1$、支撑 $d\le Z$。合成权
\[
\lambda^+(d)=\sum_{[e,f]=d}\rho_e\rho_f
\]
支撑于 $d\le Z^2$，且 $|\lambda^+(d)|\le3^{\omega(d)}$。因此矩形内三个数均为大于 $Z$ 的素数的点数至多
\[
X_0/G(Z)+O\left(\sum_{d\le Z^2}^{*}3^{\omega(d)}|r_d|\right).
\]
取 $Z=m^\kappa$，固定 $0<\kappa<1/6$，由 (2.2) 得
\[
\left(\frac{216C_2}{\kappa^3}+o(1)\right)
\frac{AB}{2mt\log^3m}
+O_\eta(m^{1/2+3\kappa+\eta}).
\tag{3.2}
\]
目标中的三个素数都大于 $z\asymp m^{2/3}$，故不会等于筛除的小素数。

## 4. 三素数深度尾界

### 定理 4.1

存在绝对常数 $K$，使对 $r\ge3$、$1\le J\le r$，
\[
C_{r,\ge J}\le K\left(\frac{m}{3^J(\log m)^2}+m^{3/5}\right).
\]

**证明。** 对 $z<a<m$ 按倍增区间分块，再用 $b$ 的倍增区间覆盖 $a<b<m^2/a$。每个矩形满足第 2 节的边长限制，矩形数 $O(\log^2m)$，且其面积和为 $O(m^2\log m)$。在 (3.2) 中固定 $\kappa=1/100$，取足够小的 $\eta$。对主项求和得 $O(m/(t\log^2m))$；余项为 $O(m^{1/2+3/100+\eta}\log^2m)=O(m^{3/5})$。有限的小 $m$ 通过增大绝对常数覆盖。$\square$

### 推论 4.2

\[
\lim_{J\to\infty}\limsup_{r\to\infty}
\frac{\log^2m}{m}C_{r,\ge J}=0.
\]

**证明。** 定理 4.1 归一化后上界为 $K(3^{-J}+m^{-2/5}\log^2m)$，依次取极限。$\square$

### 定理 4.3（显式渐近系数）

对每个固定 $J\ge1$，
\[
\limsup_{r\to\infty}\frac{3^J\log^2m}{m}C_{r,\ge J}\le7776C_2.
\]

**证明。** 固定 $\delta>0$，按比值 $1+\delta$ 分割 $a$。对一行 $a\in(u,(1+\delta)u]$，以 $b\in(u,m^2/u]$ 覆盖目标点。矩形数为 $O_\delta(\log m)$，面积和至多
\[
\left(\frac{\delta}{\log(1+\delta)}+o(1)\right)\frac{m^2\log m}{3}.
\]
对 (3.2) 求和，先令 $m\to\infty$，再依次令 $\delta\downarrow0$、$\kappa\uparrow1/6$。归一化系数为 $36C_2/\kappa^3$，其极限为 $7776C_2$。$\square$

这些结论均为上界；它们不包含 $C_r$ 的渐近等式或双素数计数的下界。

## 参考

[1] I. E. Shparlinski, *Modular Hyperbolas*, 式 (1) 及矩形分布部分：https://arxiv.org/abs/1103.2879 。使用其完全 Kloosterman 上界。

[2] K. S. Kedlaya, *Notes on analytic number theory*, Chapter 13, Theorem 13.1、(13.2.3)–(13.2.6)，及 Chapter 14 的乘法函数估计：
https://kskedlaya.org/ant/chap-selberg.html
https://kskedlaya.org/ant/chap-selberg2.html

# F₃ 精确层上的粗糙 Liouville 和

对 $n>1$，令 $F_3(n)=v_3(n+1)-v_3(n-1)$、$\lambda(n)=(-1)^{\Omega(n)}$，其中 $\Omega$ 按重数计。$P^-(n)$ 表示最小素因子，所有对数为自然对数。

对 $d\ge1$、$\sigma=\pm1$，定义
\[
\mathcal R_{d,\sigma}(X)=\{2\le n\le X:F_3(n)=\sigma d,\ P^-(n)>X^{1/3}\}.
\]
记其中素数、半素数的个数分别为 $P_{d,\sigma}(X)$、$C_{d,\sigma}(X)$，并置
\[
B_{d,\sigma}=|\mathcal R_{d,\sigma}|,\qquad
\mathscr L_{d,\sigma}=\sum_{n\in\mathcal R_{d,\sigma}}\lambda(n).
\]
粗糙条件排除三个或更多素因子，故精确有
\[
B_{d,\sigma}=P_{d,\sigma}+C_{d,\sigma},\qquad
\mathscr L_{d,\sigma}=C_{d,\sigma}-P_{d,\sigma}.
\]
半素数允许为平方。

## 1. 精确层与外部分析定理

置 $q=3^{d+1}$。正负层分别由模 $q$ 的两个约化剩余类组成：
\[
R_{d,+}=\{-1+3^d,-1+2\cdot3^d\},\qquad
R_{d,-}=\{1+3^d,1+2\cdot3^d\}.
\]
因此 $2/\varphi(q)=3^{-d}$。记
\[
A_d(X)=X/(3^d\log X).
\]

以下使用三个外部输入。

**素数幂模数的素数定理。** 对每个固定 $\varepsilon>0$，统一于 $q=3^j\le y^{5/12-\varepsilon}$ 和 $(a,q)=1$，
\[
\pi(y;q,a)=(1+o_\varepsilon(1))\frac{y}{\varphi(q)\log y}.
\tag{PNT3}
\]
这是 [1, Corollary 3.1, (3.2)] 的固定平方自由核情形。对足够大的 $q$，其 powerful-moduli 结论适用且相对误差趋零；有界 $q$ 用固定模数素数定理。由加权计数到 $\pi$ 使用分部求和，固定指数余量允许舍弃一个较短初始区间。

**经典 Brun–Titchmarsh 上界。** 对 $y>q$、$(a,q)=1$，
\[
\pi(y;q,a)\le\frac{2y}{\varphi(q)\log(y/q)}.
\tag{BT}
\]

**加强的上界。** 写 $\omega=\log q/\log y$，$\vartheta=7/64$。在固定紧子区间 $9/20<\omega<1/2$ 上，[2, v2, Theorem 1.1] 给出任意固定正余量下的系数
\[
\frac{16}{8-(3+2\vartheta)\omega}
=\frac{2}{1-(103/256)\omega}
\]
乘以 $y/(\varphi(q)\log y)$。在 $\omega<9/20$ 的紧子区间，[2, v2, §1] 所述 Iwaniec 系数 $16/(8-3\omega)$ 更强，故同一个较弱包络仍可使用。接缝 $\omega=9/20$ 单独采用 (BT)。这里只使用一般模数版本，不调用另有素数模数或平方自由假设的结果。

## 2. 精确主项

### 定理 2.1

对固定 $\varepsilon\in(0,5/24)$，统一于 $d\ge1$、$\sigma=\pm1$、$3^{d+1}\le X^{5/24-\varepsilon}$，有
\[
P_{d,\sigma}(X)=(1+o_\varepsilon(1))A_d(X),
\qquad
C_{d,\sigma}(X)=(\log2+o_\varepsilon(1))A_d(X).
\]
从而
\[
\mathscr L_{d,\sigma}(X)=(\log2-1+o_\varepsilon(1))A_d(X),
\]
\[
\frac{\mathscr L_{d,\sigma}(X)}{B_{d,\sigma}(X)}
\longrightarrow\frac{\log2-1}{\log2+1}.
\]

**证明。** 素数项直接来自 (PNT3)。删去不超过 $X^{1/3}$ 的素数，可用两个剩余类中的整数计数 $O(X^{1/3}/q+1)=o(A_d)$ 控制。

每个半素数唯一写为 $n=ab$，其中 $a,b$ 为素数、$X^{1/3}<a\le b$、$ab\le X$。设 $R=R_{d,\sigma}$。精确地，
\[
C_{d,\sigma}(X)=
\sum_{\substack{X^{1/3}<a\le\sqrt X\\a\text{ 为素数}}}
\sum_{c\in R}\left[\pi(X/a;q,ca^{-1})-\pi(a^-;q,ca^{-1})\right].
\tag{2.1}
\]
$a>3$ 保证逆元存在；减去 $a^-$ 保留且只计一次平方情形。

对 $y=X/a\ge\sqrt X$，给定的指数余量保证 (PNT3) 统一适用。普通素数定理及分部求和给出
\[
\sum_{\substack{X^\alpha<a\le X^\beta\\a\text{ 为素数}}}
\frac1{a\log(X/a)}
=\frac{1+o(1)}{\log X}\int_\alpha^\beta\frac{dt}{t(1-t)}
\]
对固定 $0<\alpha<\beta<1$ 成立。取 $\alpha=1/3,\beta=1/2$，积分等于 $\log2$。

式 (2.1) 中减去的项为低阶：$a\ge X^{1/3}$ 而 $q\le X^{5/24-\varepsilon}$，故 $\log(a/q)\gg\log X$。由 (BT)，
\[
\sum_a\sum_{c\in R}\pi(a^-;q,ca^{-1})
\ll\frac1{\varphi(q)\log X}\sum_{a\le\sqrt X\atop a\text{ 为素数}}a
\ll\frac{X}{\varphi(q)\log^2X}=o(A_d).
\]
代回即得全部结论。$\square$

## 3. 更大模数范围内的负号

### 定理 3.1

存在 $X_0$，使对所有 $X\ge X_0$、$d\ge1$、$\sigma=\pm1$，只要 $3^{d+1}\le X^{23/100}$，就有
\[
\mathscr L_{d,\sigma}(X)\le-\frac1{500}\frac{X}{3^d\log X}<0.
\]

**证明。** 素数项仍满足 $P=(1+o(1))A_d$，因为 $23/100<5/12$。令 $s=447/1000$，在式 (2.1) 中丢掉非负减项，并按 $a\le X^s$ 或 $a>X^s$ 分割。

第一段的 $y=X/a$ 至少为 $X^{1-s}$，且
\[
(1-s)\frac5{12}-\frac{23}{100}=\frac1{2400}>0.
\]
故 (PNT3) 给出上界系数 $\int_{1/3}^s dt/(t(1-t))$。

第二段写 $\eta=\log q/\log X\le23/100$、$t=\log a/\log X$，则 $\omega=\eta/(1-t)\le0.46<1/2$。除接缝外使用第 1 节的加强包络，再用普通素数定理分部求和，所得系数至多
\[
2\int_s^{1/2}\frac{dt}{t(1-t-(103/256)(23/100))}+o(1).
\]
对 $\eta\le1/5$，也可直接应用定理 2.1，故只需在 $\eta\in[1/5,23/100]$ 的固定范围内讨论统一误差。

取 $\delta_0=10^{-6}$。在 $|\omega-9/20|\le\delta_0$ 的接缝区间改用 (BT)。由 $t=1-\eta/\omega$，该区间长度至多
\[
\frac{2\delta_0(23/100)}{(9/20-\delta_0)^2}.
\]
在相关范围内 $1/(t(1-t))<5$，经典 (BT) 的相对系数小于 $4$。把整个接缝质量额外加入，付出的系数小于
\[
20\frac{2\delta_0(23/100)}{(9/20-\delta_0)^2}<10^{-4}.
\]
接缝外位于固定紧子区间，可统一使用文献中的任意小常数余量。

两个积分之和精确等于
\[
\mathcal C=\log\frac{894}{553}
+\frac{51200}{23231}\log\frac{5893900}{4662657}.
\]
有严格不等式 $\mathcal C+10^{-4}<997/1000$。一个纯有理数核对为：对 $x>1$ 置 $u=(x-1)/(x+1)$，则
\[
2\sum_{k=0}^{11}\frac{u^{2k+1}}{2k+1}
<\log x<
2\sum_{k=0}^{11}\frac{u^{2k+1}}{2k+1}
+\frac{2u^{25}}{25(1-u^2)}.
\]
分别代入上述两个有理数 $x$，取上界并通分，即得到所列严格比较。

因此 $C\le(0.997+o(1))A_d$，而 $P=(1+o(1))A_d$。先将文献中的固定常数损失取得足够小，再令 $X$ 足够大，保留 $1/500$ 的间隙。$\square$

本定理不附加 $n-2$ 或 $n+2$ 为素数的条件；也不涵盖模数约为 $X^{1/2}$ 的增长层。$X_0$ 的数值未在此确定。

## 参考

[1] J. Thorner and A. Zaman, *Refinements to the prime number theorem for arithmetic progressions*, arXiv:2108.10878v2, Corollary 3.1, (3.2)：
https://arxiv.org/abs/2108.10878v2

[2] P. Xi and J. Zheng, *On the Brun–Titchmarsh theorem*, arXiv:2404.01003v2, Theorem 1.1 and §1：
https://arxiv.org/abs/2404.01003v2

这里的具体系数采用上述固定版本。普通素数定理、分部求和与经典 Brun–Titchmarsh 不等式同样作为外部定理使用。

# 二次赋值差分权与有限求和

对 $r\ge1$，置 $Q=3^{2r}$、$m=3^r$、$q=Q/3$，并定义
\[
W_r(z)=3\mathbf1_{Q\mid z}-\mathbf1_{q\mid z},\qquad
w_{r,h}(n)=W_r(n(n+h)+1).
\]
定义只使用整除指标，故 $W_r(0)=2$。对 $n>1$、$h\ge0$，
\[
w_{r,h}(n)=3\mathbf1_{F_3(n(n+h))\ge2r}-\mathbf1_{F_3(n(n+h))\ge2r-1}.
\]
这是因为两个邻数相差 $2$，任意正赋值阈值都可由 $F_3$ 读取。

## 1. 有限驻相与二次传递

### 定理 1.1

设 $\ell$ 为奇素数，$M=\ell^r$，$P\in\mathbb Z[x]$，并令
\[
W_{\ell,r}(z)=\ell\mathbf1_{M^2\mid z}-\mathbf1_{M^2/\ell\mid z}.
\]
则
\[
\sum_{n\bmod M^2}W_{\ell,r}(P(n))
=M\sum_{\substack{a\bmod M\\P'(a)\equiv0\ (M)}}W_{\ell,r}(P(a)).
\]

**证明。** 唯一写 $n=a+Mb$，$a,b\bmod M$。Taylor 展开在模 $M^2$ 下给出
\[
P(a+Mb)\equiv P(a)+MP'(a)b.
\]
若 $M\mid P'(a)$，本块恒值为 $MW_{\ell,r}(P(a))$。否则写 $v_\ell(P'(a))=s<r$。线性项遍历 $\ell^{r+s}$ 生成的子群，每个值重复 $\ell^s$ 次。常数项不被 $\ell^{r+s}$ 整除时两种整除条件都无解；整除时，两个解数分别为 $\ell^s$ 和 $\ell^{s+1}$，加权后为零。驻点类内 $P(a)\bmod M^2$ 与代表选择无关。$\square$

### 推论 1.2（二次判别式传递）

若 $P(n)=An^2+Bn+C$、$\ell\nmid A$，则
\[
\sum_{n\bmod\ell^{2r}}W_{\ell,r}(P(n))
=\ell^rW_{\ell,r}(B^2-4AC).
\]

**证明。** $y=2An+B$ 为模 $\ell^{2r}$ 的置换，且 $4AP(n)=y^2-(B^2-4AC)$。权不受单位因子影响。对 $y^2-D$ 应用定理 1.1，唯一驻点类是 $y\equiv0\pmod{\ell^r}$。$\square$

特别地，若 $a_c\bmod m$ 是 $2a_c+h\equiv0\pmod m$ 的唯一类，则
\[
\sum_{b\bmod m}w_{r,h}(a+mb)
=mW_r(h^2-4)\mathbf1_{a=a_c}.
\]
故对任意 $B:\mathbb Z/m\mathbb Z\to\mathbb C$，
\[
\sum_{n\bmod Q}B(n\bmod m)w_{r,h}(n)=mB(a_c)W_r(h^2-4).
\]

### 推论 1.3（短位移）

若 $2\le H<q-2$、$2\le h\le H$，则
\[
Q^{-1}\sum_{n\bmod Q}w_{r,h}(n)=\mathbf1_{h=2}\,2/3^r.
\]
且 $w_{r,2}(n)=2\mathbf1_{m\mid n+1}$。

**证明。** $n(n+2)+1=(n+1)^2$。当 $h>2$ 时，$h-2,h+2$ 均严格位于 $(0,q)$，且相差 $4$，故至多一个被 $3$ 整除，从而 $q\nmid h^2-4$。使用推论 1.2。$\square$

## 2. 根计数与两支差分

令 $R_R(h)$ 为 $n(n+h)+1\equiv0\pmod{3^R}$ 的根数。若 $D=h^2-4$ 被 $3^R$ 整除，则
\[
R_R(h)=3^{\lfloor R/2\rfloor}.
\]
否则令 $v_3(D)=v<R$、$u=D/3^v$，则
\[
R_R(h)=\begin{cases}
2\cdot3^{v/2},&v\text{ 偶且 }u\equiv1\pmod3,\\
0,&\text{否则}.
\end{cases}
\]

**证明。** 完成平方将问题化为 $y^2\equiv D\pmod{3^R}$。零判别式类要求 $3^{\lceil R/2\rceil}\mid y$。其余情形中根必须有赋值 $v/2$，故 $v$ 为偶数。约去 $3^v$ 后，单位平方根存在当且仅当 $u\equiv1\pmod3$，两个简单根各自唯一提升；每根产生 $3^{v/2}$ 个原变量类。$\square$

### 定理 2.1（两支差分分解）

设 $h>2$ 且 $v_3(h^2-4)<2r-1$。若该赋值为奇数，或单位部分非平方，则 $w_{r,h}\equiv0$。否则写
\[
v_3(h^2-4)=2s,\quad L=2r-s,\quad M=3^L.
\]
存在 $\alpha_+,\alpha_-\in\mathbb Z_3$，使
\[
w_{r,h}(n)=\psi_{L,\alpha_+}(n)+\psi_{L,\alpha_-}(n),
\quad
\psi_{L,a}(n)=3\mathbf1_{n\equiv a\ (3^L)}-\mathbf1_{n\equiv a\ (3^{L-1})}.
\]
两个父类不交；每个父类三个子类的权为 $(2,-1,-1)$ 的一个排列。

**证明。** 两个根由单位平方根提升给出，且 $v_3(\alpha_+-\alpha_-)=s$。对 $R>2s$，因
\[
n(n+h)+1=(n-\alpha_+)(n-\alpha_-),
\]
赋值至少为 $R$ 当且仅当 $n\equiv\alpha_\pm\pmod{3^{R-s}}$。分别代入 $R=2r,2r-1$ 并相减。$L-1>s$ 保证父类不交。$\square$

在一个模 $M$ 周期内，正权点有两个，负权点有四个，因此
\[
\sum|w_{r,h}|=8,\qquad\sum w_{r,h}^2=12.
\]
归一化 Fourier 系数满足
\[
\widehat\psi_{L,a}(u)=\begin{cases}(3/M)e_M(-ua),&3\nmid u,\\0,&3\mid u.
\end{cases}
\]
两支相加的非零频率不消失，因为两个相位之比具有奇数阶，不可能等于 $-1$。故最小周期为 $M$。

## 3. 等差数列与除数和

### 定理 3.1

在推论 1.3 的窗口内，设 $h>2$，$d\ge1$、$3\nmid d$，$I$ 为有限连续整数区间。则
\[
\left|\sum_{j\in I}w_{r,h}(a+dj)\right|\le4.
\]

**证明。** 对一个 $\psi$，公差为三进单位，故父类内的点依次轮换三个子类。若父类计数为 $N$，指定子类计数与 $N/3$ 的差的绝对值至多 $2/3$，故加权和绝对值至多 $2$。两支相加得 $4$。$\square$

由分部求和，对有限复系数 $A_j$ 还得到上界
\[
4\left(|A_{\max I}|+\sum_{j,j+1\in I}|A_{j+1}-A_j|\right).
\]

### 定理 3.2

设有限支撑系数 $a_d,b_e$ 仅在 $3\nmid de$ 处非零。令
\[
A(n)=\sum_{d\mid n}a_d,\quad B(n)=\sum_{e\mid n}b_e,
\quad U=\sum|a_d|,\quad V=\sum|b_e|.
\]
则
\[
\sum_{n=1}^{X}A(n)B(n+h)w_{r,h}(n)
=\mathbf1_{h=2}\frac{2X}{3^r}\sum_{\gcd(d,e)\mid2}\frac{a_db_e}{[d,e]}+E_h,
\]
其中 $|E_h|\le4UV$；$h=2$ 时可改为 $2UV$。

**证明。** 展开除数和。条件 $d\mid n,e\mid n+h$ 可解当且仅当 $\gcd(d,e)\mid h$，此时组成公差 $[d,e]$ 的等差数列。$h>2$ 用定理 3.1。$h=2$ 时再加入 $n\equiv-1\pmod{3^r}$，中国剩余定理给出唯一模 $3^r[d,e]$ 的类，其计数为 $X/(3^r[d,e])+O(1)$。$\square$

## 4. 活跃偶位移与绝对质量

### 定理 4.1

在 $2<h\le H<q-2$ 的偶位移中，$w_{r,h}$ 非零当且仅当存在唯一 $s\ge1$，使
\[
h\equiv2\cdot9^s-2\quad\text{或}\quad4\cdot9^s+2\pmod{6\cdot9^s}.
\]
此时 $s\le r-1$。

**证明。** 令 $x=h/2$。$D=4(x-1)(x+1)$，两个因子至多一个含 $3$。可解时写 $x=\epsilon+3^{2s}u$，则 $D/3^{2s}\equiv2\epsilon u\pmod3$。单位平方条件等价于 $u\equiv-\epsilon\pmod3$。换回 $h$ 即得两个偶剩余类。$\square$

令 $A_s(H)$ 为这一层的位移集合，
\[
N(H)=\sum_s|A_s(H)|,\qquad A(H)=\sum_s3^s|A_s(H)|.
\]
则
\[
N(H)\le H/9,\qquad A(H)\le H/2,
\]
并有 $N(H)=H/24+O(\log(H+2))$、$A(H)=H/6+O(\sqrt{H+2})$。

**证明。** 置 $K=\lfloor H/2\rfloor$。在 $2\le x\le K$ 中，$x\equiv\pm1\pmod{9^s}$ 的计数为
\[
\left\lfloor\frac{K-1}{9^s}\right\rfloor+\left\lfloor\frac{K+1}{9^s}\right\rfloor\le H/9^s.
\]
所有活跃位移都属于 $s=1$ 的这两个类，且逐层求和 $3^sH/9^s$ 给出第二界。渐近式由每层两个公差 $6\cdot9^s$ 的数列计数及几何级数尾部得到。$\square$

### 定理 4.2（稀疏窗口界）

对 $X\ge1$，
\[
\sum_{\substack{4\le h\le H\\h\text{ 偶}}}\sum_{n=1}^{X}|w_{r,h}(n)|
\le\frac{8XA(H)}Q+4N(H)
\le\frac{4XH}Q+\frac{4H}9.
\]

**证明。** 每支差分满足 $|\psi|=\mathbf1_{\text{父类}}+\mathbf1_{\text{正子类}}$。计数各剩余类的舍入误差不超过 $1$，故一个活跃位移的绝对质量至多 $8X/3^{2r-s}+4$。求和即得。$\square$

当 $X=Q$ 时，非目标整数候选恰有 $6A(H)$ 个，其中 $2A(H)$ 个权为 $2$、$4A(H)$ 个权为 $-1$。因而给这些候选附加任意 $[0,1]$ 权后，总和属于 $[-4A(H),4A(H)]$。

取 $H=240$，有 $A(H)=36$，故对 $r\ge3$ 上界为 $144$。若仅保留奇数端点且 $r\ge5$，上界可改为 $72$。

**证明后一个改进。** 此时 $q>H^2/4$，非目标支撑在 $[Q-h,Q]$ 内为空：写 $u=Q-n\in[0,h]$，则多项式模 $q$ 等于非零整数 $1-u(h-u)$，其绝对值小于 $q$。其余支撑上的 $n\mapsto Q-h-n$ 是保权、翻转奇偶的对合，故正负容量均减半。$\square$

## 5. 一个素数输入的平均

固定 $r,H$ 满足上述窗口。则
\[
\lim_{X\to\infty}\frac1{\pi(X)}\sum_{\substack{3<p\le X\\p\text{ 为素数}}}w_{r,h}(p)
=\mathbf1_{h=2}\,3^{1-r}.
\]

**证明。** $h=2$ 的和等于 $2\pi(X;3^r,-1)$，至多差有限项。其余非零权的两支差分均支撑在约化剩余类，等差数列素数定理使每支主项 $3/\varphi(M)-1/\varphi(M/3)$ 抵消。$\square$

Siegel–Walfisz 定理还给出：固定 $A,B>0$，统一于 $Q\le(\log X)^B$ 和上述位移窗口，
\[
\sum_{3<p\le X}w_{r,h}(p)
=\mathbf1_{h=2}3^{1-r}\operatorname{Li}(X)+O_{A,B}(X/(\log X)^A).
\]
该计数不附加 $p+h$ 为素数的条件。

## 参考

第 1–4 节由有限同余计数给出证明。第 5 节使用固定模数素数定理及 Siegel–Walfisz 定理；参见 J. Thorner and A. Zaman, *Refinements to the prime number theorem for arithmetic progressions*, §§1.1–1.2：https://arxiv.org/abs/2108.10878 。

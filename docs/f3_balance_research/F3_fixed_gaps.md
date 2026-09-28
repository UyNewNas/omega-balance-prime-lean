# 固定间距的平方坐标与联合深度律

对 $n>1$ 定义 $F_3(n)=v_3(n+1)-v_3(n-1)$。在 $\mathbb Z_3\setminus\{\pm1\}$ 上使用同一公式，并约定 $v_3(0)=+\infty$ 仅用于多项式的零点。概率均相对于所述集合上的归一化加法 Haar 测度；有限个多项式零点是零测集。

固定 $k\ge1$，令
\[
\mathcal S_k=\{n\in\mathbb Z_3:v_3(n+1)=k\}.
\]
它在 $\mathbb Z_3$ 中的测度为 $2/3^{k+1}$。对 $h\equiv2\pmod3$，定义
\[
D_h(n)=v_3(n(n+h)+1).
\]
当 $n>1$、$h>0$ 为整数且 $F_3(n)=k$ 时，$D_h(n)=F_3(n(n+h))$。

## 1. 固定层的确定性分类

### 定理 1.1

写 $n=-1+3^ka$，$a\in\mathbb Z_3^\times$。令 $d=v_3(h-2)$，在 $h=2$ 时取 $d=+\infty$。则
\[
D_h(n)=\min(2k,d)\quad(d\ne2k).
\]
当 $h-2=3^{2k}c$、$3\nmid c$ 时，
\[
D_h(n)=2k+v_3(a^2+3^kca-c).
\]
因此
\[
D_h(n)>2k\iff h\equiv2+3^{2k}\pmod{3^{2k+1}}.
\]
该条件成立时，$F_3(n+h)=-k$。

**证明。** 直接展开
\[
n(n+h)+1=3^{2k}a^2-(h-2)(1-3^ka).
\]
两项赋值不等时取较小者；相等时除去 $3^{2k}$。每个三进单位满足 $a^2\equiv1\pmod3$，故余式模 $3$ 为 $1-c$。最后，$n+h-1=3^ka+(h-2)$ 的赋值为 $k$。$\square$

### 推论 1.2（锐性间距界）

若 $h$ 为正偶数且 $D_h(n)>2k$，则 $h\ge2+4\cdot3^{2k}$。该界在奇整数输入上对每个 $k$ 都可达到。

**证明。** $h=2+3^{2k}c$ 中的 $c$ 必为正偶数且同余于 $1\pmod3$，故 $c\ge4$。取 $A=2\cdot3^k$、$n=A-1$、$q=A^2+A+1$，则
\[
q-n=2+4\cdot3^{2k},\quad F_3(n)=k,\quad F_3(q)=-k,\quad nq+1=A^3.
\]
因而 $F_3(nq)=3k$。$\square$

## 2. 迹坐标的平方正规形

对 $n\in-1+3\mathbb Z_3$，定义
\[
\Gamma(n)=-n-n^{-1}.
\]
则
\[
n(n+h)+1=n(h-\Gamma(n)),\qquad
\Gamma(n)-2=-\frac{(n+1)^2}{n}.
\]

### 定理 2.1

存在从 $-1+3\mathbb Z_3$ 到 $3\mathbb Z_3$ 的双射等距坐标 $y$，使
\[
\Gamma(n)=2+y^2,\qquad
D_h(n)=v_3(y^2-(h-2)),\qquad
v_3(y)=v_3(n+1).
\]
且 $y(n^{-1})=-y(n)$。

**证明。** Hensel 引理给出唯一 $u=\sqrt{-n}\in1+3\mathbb Z_3$。置
\[
y=(n+1)/u=u^{-1}-u.
\]
直接代入得到恒等式。反向给定 $y\in3\mathbb Z_3$，方程 $u^2+yu-1=0$ 模 $3$ 在 $u=1$ 处为简单根，故有唯一 $u\in1+3\mathbb Z_3$，再取 $n=-u^2$。若 $u,u'$ 为两个这样的参数，则
\[
n-n'=-(u-u')(u+u'),\qquad
y-y'=-(u-u')(1+(uu')^{-1}).
\]
两个括号均为三进单位，故映射等距。对 $n^{-1}$，平方根为 $u^{-1}$，给出反号。$\square$

除 $n=-1$ 外，$\Gamma$ 的每个纤维恰为 $\{n,n^{-1}\}$：平方坐标中的两个原像为 $y,-y$。

## 3. 固定层的均匀坐标

### 定理 3.1

对 $n\in\mathcal S_k$，唯一写成
\[
\Gamma(n)=2+3^{2k}(1+3Z_k(n)).
\]
当 $n$ 在 $\mathcal S_k$ 均匀分布时，$Z_k(n)$ 在 $\mathbb Z_3$ 均匀分布。

**证明。** 定理 2.1 的等距双射保持有限剩余类上的均匀计数。写 $y=3^k a$，则 $a$ 在三进单位中均匀。平方映射从 $a\equiv1\pmod3$ 和 $a\equiv-1\pmod3$ 两支分别等距双射到 $1+3\mathbb Z_3$：每个目标有两个简单根，且在每支内 $a+a'$ 为单位。令 $a^2=1+3Z$ 即得。$\square$

有限形式如下：若 $a=(n+1)/3^k$，则
\[
Z_k(n)=\frac1{3}\left(\frac{a^2}{1-3^ka}-1\right).
\]
对每个 $T\ge0$，将 $a$ 遍历模 $3^{T+1}$ 的单位类，$Z_k\bmod3^T$ 的每个值恰有两个原像。因为对 $w\in1+3\mathbb Z_3$，方程 $a^2+3^kwa-w=0$ 模 $3$ 有两个简单根。

## 4. 单移位与多移位联合律

称 $h$ 在层 $k$ 共振，当
\[
h=2+3^{2k}(1+3b),\qquad b\in\mathbb Z_3.
\]
此时
\[
D_h(n)=2k+1+v_3(Z_k(n)-b).
\]
所以对 $t\ge0$，
\[
\Pr(D_h\ge2k+1+t)=3^{-t},\qquad
\Pr(D_h=2k+1+t)=2/3^{t+1}.
\]
非共振移位的值由定理 1.1 确定。

### 定理 4.1（联合尾律）

设 $h_i=2+3^{2k}(1+3b_i)$，$1\le i\le q$，$t_i\ge0$，$T=\max_i t_i$。则
\[
\Pr\bigl(D_{h_i}\ge2k+1+t_i\ \forall i\bigr)
=\begin{cases}
3^{-T},&b_i\equiv b_j\pmod{3^{\min(t_i,t_j)}}\ \forall i,j,\\
0,&\text{否则}.
\end{cases}
\]

**证明。** 事件等价于均匀的单个 $Z_k$ 同时满足 $Z_k\equiv b_i\pmod{3^{t_i}}$。这些嵌套模数的同余两两相容时，交集恰为模 $3^T$ 的一个剩余类；否则交集为空。$\square$

### 推论 4.2

对 $h_i\ne h_j$，
\[
\min(D_{h_i}(n),D_{h_j}(n))\le v_3(h_i-h_j),
\]
且两个深度不等时取等号。

**证明。** 两个多项式值之差为 $(h_i-h_j)n$，而 $n$ 为单位。使用非阿基米德三角不等式及不等赋值时的等号条件。$\square$

取
\[
h_0=2+4\cdot3^{2k},\quad h_1=2+10\cdot3^{2k},\quad h_2=2+16\cdot3^{2k}.
\]
三个对应的 $b$ 分别为 $1,3,5$，遍历模 $3$ 的全部类。因此三个 $D_{h_i}$ 均至少为 $2k+1$，其中恰一个至少为 $2k+2$，另两个恰为 $2k+1$。

## 5. 固定正间距的有界性

设 $h>0$、$h\equiv2\pmod3$、$h\ne2$，写 $h-2=3^d c$、$3\nmid c$。

若 $d$ 为奇数，或 $d$ 为偶数且 $c\equiv2\pmod3$，则对全部 $n\equiv-1\pmod3$ 有 $D_h(n)\le d$，且上界可由正整数达到。若 $d=2k$ 且 $c\equiv1\pmod3$，则存在两条可以任意提升的根分支；所有 $D_h(n)>d$ 的输入均满足 $F_3(n)=k$、$F_3(n+h)=-k$。

**证明。** $h+2\equiv1\pmod3$，故判别式 $h^2-4$ 的赋值和单位首位与 $h-2$ 相同。完成平方
\[
4(n^2+hn+1)=(2n+h)^2-(h^2-4)
\]
并使用奇素数处的平方判据，即得两种情形。或者逐层应用定理 1.1 和第 4 节的尾律。$\square$

## 6. 一个素数输入上的联合计数

固定 $k$、共振移位 $h_i$ 和门槛 $t_i$。若定理 4.1 的同余条件相容，则
\[
\#\{p\le X:p\text{ 为素数},\ F_3(p)=k,\ D_{h_i}(p)\ge2k+1+t_i\ \forall i\}
\sim3^{-(k+T)}\operatorname{Li}(X).
\]
若条件不相容，则计数为零。

**证明。** 第 3 节的有限均匀坐标将相容事件对应到模 $3^{k+T+1}$ 的两个约化剩余类。固定模数的等差数列素数定理给出系数 $2/\varphi(3^{k+T+1})=3^{-(k+T)}$。$\square$

此定理只要求输入 $p$ 为素数，不要求任何 $p+h_i$ 为素数。

### 命题 6.1（有限局部模式的合数伴随实现）

设 $h_1,\ldots,h_q$ 是非零正整数。一组局部条件若包含某个约化剩余类 $n\equiv a\pmod{3^R}$，则存在无穷多个素数 $p$ 满足这些条件，同时每个 $p+h_i$ 均为合数。

**证明。** 选取互不相同的素数 $\ell_i$，使 $\ell_i\nmid3h_i$，并附加 $p\equiv-h_i\pmod{\ell_i}$。中国剩余定理将这些条件合成为一个约化剩余类。Dirichlet 定理给出其中无穷多个素数 $p$；当 $p$ 足够大时，每个伴随数都被 $\ell_i$ 真整除。$\square$

非奇异表达式的有限个有限赋值条件在其定义点附近局部常值，故若可实现，就包含这样的剩余类。本命题不适用于把精度随 $X$ 增长的条件当作一个固定模数处理。

## 参考

- K. Conrad, *Hensel's Lemma*, Theorem 2.1：https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf 。
- W. Boultinghouse et al., *The p-Adic Valuation Trees for Quadratic Polynomials for Odd Primes*, Theorems 1.1–1.2：https://arxiv.org/abs/2309.16637 。第 5 节是一般二次赋值分类的特例。
- J. Thorner and A. Zaman, *Refinements to the prime number theorem for arithmetic progressions*, §1.1：https://arxiv.org/abs/2108.10878 。第 6 节只使用固定模数的素数定理。

# F₃ 的算术结构

对非零整数 $x$，以 $v_3(x)$ 表示 $|x|$ 中因子 $3$ 的重数。对整数 $n>1$，定义
\[
F_3(n)=v_3(n+1)-v_3(n-1),\qquad d(n)=|F_3(n)|.
\]
本文件中的赋值自变量均非零。$\Omega(n)$ 始终按重数计，$\lambda(n)=(-1)^{\Omega(n)}$；$\Lambda$ 表示 von Mangoldt 函数。

## 1. 符号与幂

### 命题 1.1

对 $n>1$，有
\[
F_3(n)=\begin{cases}
0,&n\equiv0\pmod3,\\
-v_3(n-1)<0,&n\equiv1\pmod3,\\
v_3(n+1)>0,&n\equiv-1\pmod3.
\end{cases}
\]

**证明。** $n+1$ 与 $n-1$ 相差 $2$，不可能同时被 $3$ 整除。逐个检查 $n$ 模 $3$ 的剩余类即可。$\square$

### 定理 1.2（幂深度）

设 $n>1$、$3\nmid n$、$e\ge1$。取 $\epsilon\in\{\pm1\}$ 满足 $n\equiv\epsilon\pmod3$。则
\[
d(n^e)=d(n)+v_3(e),\qquad
F_3(n^e)=-\epsilon^e\bigl(d(n)+v_3(e)\bigr).
\]

**证明。** 令 $U=\epsilon n\equiv1\pmod3$。由命题 1.1，$v_3(U-1)=d(n)$ 且 $d(n^e)=v_3(U^e-1)$。若 $3\nmid h$，则
\[
\frac{U^h-1}{U-1}=1+U+\cdots+U^{h-1}\equiv h\not\equiv0\pmod3,
\]
故取 $h$ 次幂不改变深度。若 $U=1+3^d u$，$d\ge1$、$3\nmid u$，则
\[
U^2+U+1=3\left(1+3^du+3^{2d-1}u^2\right)
\]
的赋值为 $1$，故每次立方增加深度 $1$。写 $e=3^s h$ 得深度公式；符号由 $n^e\equiv\epsilon^e\pmod3$ 决定。$\square$

## 2. 相反层与乘积深度

### 定理 2.1（和积二分）

设 $p,q>1$，$k\ge1$，$F_3(p)=k$、$F_3(q)=-k$。则
\[
\min\{v_3(p+q),v_3(pq+1)\}=k,
\qquad v_3(p+q)\ne v_3(pq+1).
\]

**证明。** 写 $p+1=3^k a$、$q-1=3^k b$，其中 $a,b$ 为正的三进单位。于是
\[
p+q=3^k(a+b),\qquad pq+1=3^k(a+pb).
\]
模 $3$ 下，$p\equiv-1$，所以两个余因子分别同余于 $a+b$ 与 $a-b$。三进单位只有两个非零首位，故这两个余因子恰好一个被 $3$ 整除。$\square$

### 定理 2.2（间距分类）

进一步设 $p<q$ 且两者为奇数。令 $\Delta=q-p-2\ge0$，$s=F_3(pq)$。
若 $\Delta=0$，则 $s=2k$。若 $\Delta>0$，令 $v=v_3(\Delta)$，则 $v\ge k$，并有
\[
v\ne2k\Longrightarrow s=\min(2k,v).
\]
若 $v=2k$，写 $\Delta=3^{2k}u$，则
\[
s>2k\iff u\equiv1\pmod3,
\qquad s=2k\iff u\equiv2\pmod3.
\]
特别地，
\[
s\ge2k\iff3^{2k}\mid\Delta.
\]
在此整除条件下写 $\Delta=2\cdot3^{2k}h$，则
\[
s>2k\iff h\equiv2\pmod3,
\qquad s>2k\Longrightarrow q-p\ge2+4\cdot3^{2k}.
\]

**证明。** 由 $q-1-(p+1)=\Delta$ 知 $3^k\mid\Delta$。$pq\equiv-1\pmod3$，故 $s=v_3(pq+1)$。恒等式
\[
pq+1=(p+1)^2+p\Delta
\]
给出不等赋值时的结论。若 $p+1=3^k a$ 且 $\Delta=3^{2k}u$，则
\[
pq+1=3^{2k}(a^2-u+3^kau).
\]
括号模 $3$ 等于 $1-u$，得临界分类。其余结论再使用 $\Delta$ 为偶数即可。$\square$

### 推论 2.3（孪生乘积）

若 $n>1$、$n\equiv-1\pmod3$，则
\[
F_3(n+2)=-F_3(n),\qquad F_3(n(n+2))=2F_3(n).
\]
特别地，两式适用于 $p,p+2$ 为素数且 $p>3$ 的情形。

**证明。** $n+2-1=n+1$，而两个外侧邻数均不被 $3$ 整除。另有 $n(n+2)+1=(n+1)^2$。孪生素数大于 $3$ 时，两端均不能被 $3$ 整除，故中点被 $3$ 整除。$\square$

## 3. 完全幂的尖锐深度界

### 定理 3.1

若 $N>1$ 为奇数、$3\nmid N$，且 $N$ 是非平凡完全幂，则
\[
81N\ge125\cdot3^{2d(N)}.
\]
等号当且仅当 $N=125$。因此，奇数单位 $N>1$ 满足 $N\le3^{2d(N)}$ 时，不是非平凡完全幂。

**证明。** 从完全幂的指数中取一个素因子 $\ell$，写 $N=a^\ell$。令 $d=d(a)\ge1$。$a-\epsilon$ 是 $3^d$ 的非零偶数倍，其中 $\epsilon\equiv a\pmod3$、$\epsilon=\pm1$，故 $a\ge2\cdot3^d-1$。

若 $\ell\ne3$，定理 1.2 给出 $d(N)=d$，于是
\[
\frac{N}{3^{2d(N)}}\ge\frac{a^2}{3^{2d}}
\ge(2-3^{-d})^2\ge25/9>125/81.
\]
若 $\ell=3$，则 $d(N)=d+1$。置 $x=3^d\ge3$，得到
\[
\frac{N}{3^{2d(N)}}\ge\frac{(2x-1)^3}{9x^2}
=\frac{x}{9}(2-x^{-1})^3\ge125/81.
\]
最后的函数在 $x\ge3$ 严格递增，等号要求 $x=3$、$a=5$。直接代入 $125$ 即得等号。$\square$

### 推论 3.2

在奇数单位区域 $1<N\le3^{2d(N)}$ 内，
\[
\Lambda(N)=\log N\,\mathbf1_{N\text{ 为素数}}.
\]

**证明。** von Mangoldt 函数只在素数幂上非零，定理 3.1 排除了高次素数幂。$\square$

## 4. 逆元因子的同层性

### 定理 4.1

设 $m=3^r$，$a,b>1$ 为奇数，$a\le b$，$ab<m^2$ 且 $ab\equiv1\pmod m$。则存在 $1\le j<r$ 与 $\epsilon=\pm1$，使
\[
F_3(a)=F_3(b)=-\epsilon j.
\]
若写 $a=\epsilon+3^jA$、$b=\epsilon+3^jB$，则乘积条件等价于
\[
A+B+\epsilon3^jAB\equiv0\pmod{3^{r-j}}.
\]

**证明。** $a\le\sqrt{ab}<m$。奇数 $a>1$ 不可能同余于 $\pm1\pmod m$，否则最小可能值至少为 $2m-1$。取 $\epsilon\equiv a\pmod3$，故 $j=v_3(a-\epsilon)<r$。由
\[
a(b-\epsilon)\equiv-\epsilon(a-\epsilon)\pmod m
\]
知 $v_3(b-\epsilon)=j$；符号也相同。展开 $ab-1$ 得最后的同余。$\square$

## 5. 深层候选与 Liouville 恒等式

设 $r\ge1$、$m=3^r$、$X=m^2$、$K=(m-1)/2$。奇数 $p>3$ 满足 $p\le X$、$F_3(p)\ge r$，当且仅当
\[
p=2mk-1,\qquad1\le k\le K.
\]
相应地，
\[
F_3(2mk-1)=r+v_3(k),\quad
F_3(2mk+1)=-(r+v_3(k)).
\]
这由 $m\mid p+1$ 和 $p+1$ 为偶数直接得到。两个端点都属于 $(m,m^2)$，因而由定理 3.1 均不是真幂。

令 $z=\lfloor m^{2/3}\rfloor$，定义
\[
\mathcal B_r=\{1\le k\le K:2mk-1\text{ 为素数},\ P^-(2mk+1)>z\}.
\]
记 $B_r=|\mathcal B_r|$，$L_r=\sum_{k\in\mathcal B_r}\lambda(2mk+1)$，并令 $T_r$ 计数其中两端均为素数的数对。则
\[
T_r=\frac{B_r-L_r}{2}.
\]

**证明。** 右端小于 $m^2$，且每个素因子大于 $m^{2/3}$，故 $\Omega$ 只能为 $1$ 或 $2$。其素性指示函数恰为 $(1-\lambda)/2$。所有右端素数都大于 $m>z$，不会被该条件排除。$\square$

若 $C_r=B_r-T_r$，则 $C_r$ 还精确等于
\[
\sum_{\substack{z<a<m\\a\text{ 为素数}}}
\sum_{\substack{a<b<m^2/a\\b\equiv a^{-1}\ (2m)}}
\mathbf1_{b\text{ 为素数}}\mathbf1_{ab-2\text{ 为素数}}.
\]
平方排除保证 $a<b$；唯一分解给出一一对应 $k=(ab-1)/(2m)$。此式是有限计数恒等式，不包含素数存在性断言。

### 命题 5.1（初等因子尾界）

令 $C_{r,\ge J}$ 为上述和中另满足 $|F_3(a)|\ge J$ 的项数，$1\le J\le r$。则
\[
C_{r,\ge J}\le\frac m{3^J}\left(1+\frac12\log\frac mz\right)+\frac mz+2.
\]

**证明。** 置 $t=3^J$。奇数 $a$ 落在模 $2t$ 的 $\pm1$ 两类。固定 $a$ 后，$b$ 落在模 $2m$ 的一个类，故数目不超过 $m/(2a)+1$。单调积分比较给出
\[
\sum_{\substack{z<a<m\\a\equiv\pm1\ (2t)}}a^{-1}
\le2/z+t^{-1}\log(m/z),\qquad
\#\{a\}\le m/t+2.
\]
相乘求和即得。$\square$

## 参考

幂赋值公式属于经典的指数提升论证。符号、乘积及相反层的 Lean 接口见 [F3.lean](../../OmegaBalance/F3.lean)、[F3Powers.lean](../../OmegaBalance/F3Powers.lean)、[F3SumProduct.lean](../../OmegaBalance/F3SumProduct.lean)。这些链接不表示本文全部命题已经形式化。

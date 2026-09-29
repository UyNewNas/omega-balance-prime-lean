# 素数伸缩族中任意高阶乘积的深度分离

对整数 $u>1$，定义
\[
F_3(u)=v_3(u+1)-v_3(u-1).
\]
赋值只作用于非零整数。单项式的总次数按指数之和计算，允许重复使用同一输入。下列素数计数定理的阶数、层级、目标深度和所有系数均先固定，再令 $X\to\infty$。素数计数使用已知的有限复杂度线性形式素数定理 [1–3]。

## 1. 固定形状与主定理

固定整数 $k,s\ge1$。置
\[
q=3^s,\qquad b=k+s,\qquad M=3^b,\qquad
W=\prod_{\substack{\ell\le q\\\ell\text{ 为素数},\ \ell\ne3}}\ell.
\]
定义严格递增的系数
\[
(c_0,\ldots,c_{q-1})=(0,1,2,\ldots,q-2,q),
\quad h_i=MWc_i,\quad p_i=n+h_i d.
\]
令 $\mathcal Q_{k,s}(X)$ 为满足
\[
X<n,d\le2X,\qquad F_3(n)=k,
\qquad d,p_0,\ldots,p_{q-1}\text{ 全部为素数}
\]
的正整数参数对集合，记 $B_{k,s}(X)=|\mathcal Q_{k,s}(X)|$ 和
\[
D(n,d)=F_3\!\left(\prod_{i=0}^{q-1}p_i\right).
\]
定义
\[
\begin{split}
\kappa_{k,s}={}&\frac4{3^{k+2}}\left(\frac32\right)^{q+1}
\prod_{\substack{\ell\le q\\\ell\text{ prime},\ \ell\ne3}}
\left(\frac\ell{\ell-1}\right)^{q-1}
\prod_{\substack{\ell>q\\\ell\text{ prime}}}
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}.
\end{split}
\]
该乘积收敛且严格为正，见引理 3.1。

### 定理 1.1（所有低次数单项式固定，总乘积深度可指定）

在 $\mathcal Q_{k,s}(X)$ 中，对每个非负整数指数向量
$\mathbf e=(e_0,\ldots,e_{q-1})$，只要其总次数满足
\[
1\le u:=\sum_i e_i<q,
\]
就有确定性等式
\[
\boxed{
F_3\!\left(\prod_i p_i^{e_i}\right)
=(-1)^{u+1}\bigl(k+v_3(u)\bigr).
}\tag{1.1}
\]
特别地，所有非空真子集的乘积值均已固定，且它们的绝对值不超过 $k+s-1$。

同时有
\[
B_{k,s}(X)=(\kappa_{k,s}+o_{k,s}(1))\frac{X^2}{(\log X)^{q+1}}.
\tag{1.2}
\]
对每个固定整数 $R\ge b$，
\[
\boxed{
\#\{(n,d)\in\mathcal Q_{k,s}(X):D(n,d)=R\}
=\bigl(\kappa_{k,s}w_b(R)+o_{k,s,R}(1)\bigr)
\frac{X^2}{(\log X)^{q+1}},
}\tag{1.3}
\]
其中
\[
w_b(R)=\begin{cases}
1/2,&R=b,\\
3^{-(R-b)},&R>b.
\end{cases}
\]
因此每个 $R\ge b$ 都有无穷多个全素数实现，且形状 $(h_i)$ 不随 $R$ 改变。

### 两个具体阶数

当 $s=1$ 时，$q=3$、$W=2$，形状为
\[
(n,n+2\cdot3^{k+1}d,n+6\cdot3^{k+1}d).
\]
所有单点的 $F_3$ 为 $k$，所有二次单项式的 $F_3$ 为 $-k$；三因子输出取每个 $R\ge k+1$，对应比例为定理中的 $w_{k+1}(R)$。

当 $k=1,s=2$ 时，$q=9$、$M=27$、$W=70$，形状为
\[
p_i=n+1890c_i d,\qquad(c_i)=(0,1,2,3,4,5,6,7,9).
\]
总次数 $u=1,\ldots,8$ 的所有单项式，其 $F_3$ 依次为
\[
1,-1,2,-1,1,-2,1,-1.
\]
九因子总乘积可以取任意精确深度 $R\ge3$，并可要求九个端点与步长这十个数全部为素数。

## 2. 低阶刚性与最高阶的根坐标

### 引理 2.1（幂赋值）

设 $n>1$、$F_3(n)=k\ge1$，$u\ge1$。则
\[
v_3\bigl(n^u-(-1)^u\bigr)=k+v_3(u),
\qquad F_3(n^u)=(-1)^{u+1}(k+v_3(u)).
\]

**证明。** 置 $U=-n\in1+3\mathbb Z_3$，$v_3(U-1)=k$。若 $3\nmid a$，则
$(U^a-1)/(U-1)\equiv a\pmod3$。若 $U=1+3^kz$、$3\nmid z$，则
\[
U^2+U+1=3(1+3^kz+3^{2k-1}z^2)
\]
的赋值为 $1$。写 $u=3^v a$，反复立方并使用几何和，得到
$v_3(U^u-1)=k+v$。$n^u\bmod3$ 的符号决定 $F_3$ 的符号。$\square$

### 引理 2.2（低次数刚性）

设 $n>1$、$F_3(n)=k$，$q=3^s$、$M=3^{k+s}$。任取 $q$ 个正整数 $p_i>1$，若
$p_i\equiv n\pmod M$，则 (1.1) 对所有总次数小于 $q$ 的非空单项式成立。

**证明。** 单项式 $P=\prod_i p_i^{e_i}$ 满足 $P\equiv n^u\pmod M$。由于 $1\le u<3^s$，有 $v_3(u)\le s-1$。引理 2.1 给出
\[
v_3(n^u-(-1)^u)=k+v_3(u)<k+s.
\]
改变一个被 $3^{k+s}$ 整除的项不影响这个精确赋值。因此
$v_3(P-(-1)^u)=k+v_3(u)$，另一侧邻数不被 $3$ 整除，即得 (1.1)。$\square$

### 引理 2.3（系数和判据）

保留 $n,k,s,q,M$，令 $W$ 为任意正的三进单位，取任意非负整数 $c_i$。设 $p_i=n+MWc_i d$，$d>0$，并记
\[
A(n)=\frac{n^q+1}{M},\qquad C=\sum_i c_i.
\]
则 $A(n)$ 是三进单位，且存在整数多项式 $H_n$，使
\[
\prod_i p_i+1=M G_n(d),\qquad
G_n(d)=A(n)+WCn^{q-1}d+M H_n(d).
\tag{2.1}
\]
其中 $H_n(d)$ 仅含次数至少为 $2$ 的项。

若 $3\mid C$，则对所有正整数 $d$，
\[
F_3\!\left(\prod_i p_i\right)=k+s.
\tag{2.2}
\]
若 $3\nmid C$，则 $G_n$ 在每个模 $3^T$ 上都是置换，并在 $\mathbb Z_3$ 上为双射等距映射。它有唯一零点
$d_*(n)\in\mathbb Z_3^\times$，且对正整数 $d$，
\[
\boxed{F_3\!\left(\prod_i p_i\right)=k+s+v_3(d-d_*(n)).}\tag{2.3}
\]

**证明。** 引理 2.1 对 $u=q$ 给出 $v_3(n^q+1)=k+s$。展开乘积，一次项为
$MWCn^{q-1}d$，所有更高次项至少含 $M^2$，故 (2.1) 成立。因为 $q$ 为奇数，乘积模 $3$ 为 $-1$，其 $F_3$ 为 $v_3(\prod p_i+1)$。

若 $3\mid C$，则 $G_n(d)\equiv A(n)\not\equiv0\pmod3$，得到 (2.2)。若 $3\nmid C$，则
\[
G_n(d)\equiv A(n)+WCd\pmod3,\qquad G_n'(d)\equiv WC\not\equiv0\pmod3.
\]
对每个目标值，模 $3$ 恰有一个原像，每次提高精度恰有一个提升；于是 $G_n$ 在各有限商上为置换，在 $\mathbb Z_3$ 上为双射。又
\[
G_n(d)-G_n(e)=(d-e)\bigl(WCn^{q-1}+M K_n(d,e)\bigr)
\]
且括号始终为单位，故映射等距。模 $3$ 的零点不为 $0$，因此唯一零点为单位；取 $e=d_*(n)$ 即得 (2.3)。正整数输入的乘积加一为正，不会实际取到该零点。$\square$

### 推论 2.4（普通等差形状与单点移动）

普通系数 $(0,1,\ldots,q-1)$ 满足
\[
\sum c_i=q(q-1)/2\equiv0\pmod3,
\]
所以它的总乘积深度恒为 $k+s$。

把最后一个系数 $q-1$ 替换为 $q$ 后，系数和变成
\[
q(q-1)/2+1\equiv1\pmod3.
\]
于是总乘积出现唯一的单位根分支，而所有总次数小于 $q$ 的单项式仍由引理 2.2 固定。两种形状的结论均为确定性的，不要求素性。

### 引理 2.5（精确有限分布）

对主定理的形状固定任一 $n>1$、$F_3(n)=k$，在模 $3^T$ 的单位 $d$ 中均匀计数。则
\[
\Pr(G_n(d)\not\equiv0\pmod3)=1/2,
\]
并且对 $1\le t\le T$，
\[
\Pr(3^t\mid G_n(d))=\frac1{2\cdot3^{t-1}}.
\]
对 $1\le t<T$，精确赋值为 $t$ 的比例为 $3^{-t}$；顶层只表示赋值至少为 $T$。

**证明。** 引理 2.3 给出模 $3^t$ 的唯一单位根。模 $3^T$ 的 $2\cdot3^{T-1}$ 个单位中，恰有 $3^{T-t}$ 个落入该根类。相邻门槛相减即得。该比例对每个允许的 $n$ 都相同。$\square$

## 3. 全素数计数与不能截断的乘积信息

采用 [1–3] 的以下已知结论：固定的非恒定整数仿射线性形式，其线性部分两两不成比例，则在所有形式均为正且与 $X$ 同阶的凸盒 $K_X$ 中，同时取素数的计数为
\[
\left(\prod_\ell\beta_\ell+o(1)\right)
\frac{\operatorname{area}(K_X)}{(\log X)^a},\quad
\beta_\ell=\ell^{-2}\sum_{x,y\bmod\ell}
\prod_{i=1}^a\frac\ell{\ell-1}\mathbf1_{\ell\nmid\psi_i(x,y)}.
\tag{LF}
\]
这里 $a$ 是形式数。本系统有 $q+1$ 个形式，复杂度至多 $q-1$。当 $q=3$ 时只需 [1, Corollary 1.7] 的复杂度 $2$ 结论；更高阶使用 [2–3] 补齐的完整有限复杂度版本。由 von Mangoldt 加权计数得到素数指示计数时，固定一个形式取高次素数幂的点数为 $O(X^{3/2}\log X)$，其加权贡献为 $o(X^2)$；其余对数权为 $\log X+O(1)$。

### 引理 3.1（固定三进参数类的共同主系数）

取固定 $A\ge k+1$、$Q=3^A$。在任一固定参数类
$(n,d)\equiv(a_0,b_0)\pmod Q$ 中，假设 $F_3(n)=k$ 在该类上成立且 $3\nmid b_0$。则该类内 $q+1$ 个形式全部为素数的计数为
\[
\left(\frac{\mathfrak S_{q}}{Q^2}+o_{k,s,Q}(1)\right)
\frac{X^2}{(\log X)^{q+1}},
\]
其中 $\mathfrak S_q>0$ 不依赖允许类的代表，且
\[
\mathfrak S_q=\left(\frac32\right)^{q+1}
\prod_{\substack{\ell\le q\\\ell\ne3,\ \ell\text{ prime}}}
\left(\frac\ell{\ell-1}\right)^{q-1}
\prod_{\ell>q,\ \ell\text{ prime}}
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}.
\]

**证明。** 代入 $n=a_0+Qx,d=b_0+Qy$。方向为 $(0,1)$ 与 $(1,h_i)$，两两不成比例。模 $3$ 下所有形式均为规定的单位，因子为 $(3/2)^{q+1}$。

对 $\ell\ne3$，变量变换模 $\ell$ 可逆。要求 $d\ne0$ 后，令
$\nu_\ell=|\{h_i\bmod\ell\}|$，合格参数数为
$(\ell-1)(\ell-\nu_\ell)$。当 $\ell\le q$ 时，$\ell\mid W$，故 $\nu_\ell=1$；当 $\ell>q$ 时，$M,W$ 可逆且各 $c_i$ 的非零差绝对值至多 $q<\ell$，故 $\nu_\ell=q$。这些合格数全为正，局部因子正好如式所列。

对固定 $q$，尾部因子
\[
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}
=\frac{1-q/\ell}{(1-1/\ell)^q}=1+O_q(\ell^{-2}),
\]
故乘积绝对收敛到正数。参数盒面积为 $X^2/Q^2$；应用 (LF)。$\square$

**定理 1.1 的证明。** 确定性部分由引理 2.2 给出。模 $Q=3^A$ 下满足 $F_3(n)=k$、$3\nmid d$ 的参数类总数为
\[
(2\cdot3^{A-k-1})(2\cdot3^{A-1})=4\cdot3^{2A-k-2}.
\]
对引理 3.1 的固定有限个类求和，系数为
$4\mathfrak S_q/3^{k+2}=\kappa_{k,s}$，得到 (1.2)。

要判定精确事件 $D=R$，可取固定 $A\ge R+1$：乘积加一的值模 $3^{R+1}$ 由该参数类决定。对每个 $n$ 类，引理 2.5 给出相同比例 $w_b(R)$。每个合格参数类的素数主系数相同，故再次求和得到 (1.3)。每个权 $w_b(R)$ 严格为正，且 $X^2/(\log X)^{q+1}\to\infty$，得到无穷多配置。$\square$

### 推论 3.2（全部真子集信息不决定总乘积）

对每个 $k,s\ge1$，存在同一固定伸缩形状，使全部非空真子集乘积的 $F_3$ 数据保持不变，而总乘积的 $F_3$ 在全部端点和步长均为素数的参数中无界。即使补充所有总次数小于 $3^s$ 的含重复因子的单项式数据，结论仍成立。

**证明。** 这些低次数数据全部由 (1.1) 给定，且形状只依赖 $k,s$。对每个 $R\ge k+s$ 使用 (1.3)。$\square$

### 推论 3.3（不存在统一的有限次数截断）

给定任意固定次数上限 $L$，存在某个固定的全素数伸缩族，使全部总次数不超过 $L$ 的单项式 $F_3$ 值完全相同，但该族的全端点乘积深度无界。

**证明。** 取 $s$ 使 $3^s>L$，使用推论 3.2。该结论仅针对保留这些 $F_3$ 数值的资料；它不声称完整整数输入或完整三进单位坐标也不能决定乘积。$\square$

### 推论 3.4（相同计数主系数的刚性对照族）

改取普通等差形状
\[
\widetilde p_i=n+MWi d,\qquad 0\le i<q,
\]
并令 $\widetilde{\mathcal Q}_{k,s}(X)$ 采用与 $\mathcal Q_{k,s}(X)$ 相同的参数盒、输入层及全部素性要求。则
\[
|\widetilde{\mathcal Q}_{k,s}(X)|
=(\kappa_{k,s}+o_{k,s}(1))X^2/(\log X)^{q+1}.
\]
它的全部总次数小于 $q$ 的单项式数据仍为 (1.1)，但
\[
F_3\!\left(\prod_i\widetilde p_i\right)=k+s
\]
恒成立。因此两族具有相同的低次数数据和相同的全素数计数主系数，却具有不同的总乘积深度分布。

**证明。** 低次数结论与总深度恒值由引理 2.2 和推论 2.4 给出。普通系数的差绝对值小于 $q$，所以对 $\ell>q$ 仍有 $\nu_\ell=q$；对 $\ell\le q$、$\ell\ne3$ 仍有 $\nu_\ell=1$。模 $3$ 的单位条件和允许参数类数不变。故引理 3.1 的所有局部因子与其求和系数原样成立。$\square$

## 4. 任意有限局部乘积模式的伸缩实现

### 定理 4.1（有限剩余类的素数实现）

给定端点数 $v\ge2$、$A\ge1$，令 $Q=3^A$。任取模 $Q$ 的单位 $a_0,\ldots,a_{v-1}$ 和 $b_0$。存在固定整数
\[
0=h_0<h_1<\cdots<h_{v-1},
\]
使满足
\[
(n,d)\equiv(a_0,b_0)\pmod Q,\quad X<n,d\le2X,
\qquad d,n+h_0d,\ldots,n+h_{v-1}d\text{ 全部为素数}
\]
的参数对数为 $(c+o(1))X^2/(\log X)^{v+1}$，其中 $c>0$，且每个端点满足 $n+h_i d\equiv a_i\pmod Q$。

**证明。** 令 $P$ 为不超过 $v$ 且不等于 $3$ 的全部素数的乘积。对 $i\ge1$，用中国剩余定理选取
\[
h_i\equiv(a_i-a_0)b_0^{-1}\pmod Q,\qquad h_i\equiv0\pmod P,
\]
再逐次加上 $QP$ 的倍数使其严格递增。各方向 $(0,1),(1,h_i)$ 两两不成比例。模 $3$ 的形式全部为单位。模 $\ell\ne3$ 下，令 $\nu_\ell=|\{h_i\bmod\ell\}|$。若 $\ell\le v$ 则 $\nu_\ell=1<\ell$，若 $\ell>v$ 则 $\nu_\ell\le v<\ell$，故全部局部因子为正。除有限多个整除非零 $h_i-h_j$ 的素数外，局部因子为
\[
\ell^{v-1}(\ell-v)/(\ell-1)^v=1+O_v(\ell^{-2}).
\]
乘积收敛到正数，应用 (LF)。$\square$

### 推论 4.2（有限单项式模式）

给定有限个非零非负整数指数向量 $\mathbf e_\alpha$，并规定
\[
F_3\!\left(\prod_i x_i^{e_{\alpha,i}}\right)=f_\alpha,
\]
其中各 $f_\alpha$ 为有限非零整数。若某组三进单位 $x_i$ 实现这些等式，且所涉乘积不等于 $\pm1$，则存在某个固定伸缩形状，使同样的等式由无穷多组素数端点 $p_i=n+h_i d$ 实现，且 $d$ 为素数。

**证明。** 取 $A>\max_\alpha|f_\alpha|$。这些精确赋值在模 $3^A$ 的相应单位类内不变。令 $a_i=x_i\bmod3^A$，对任意单位步长类应用定理 4.1。所有正整数端点的非空单项式大于 $1$，所需等式保留。$\square$

本节的形状允许依赖整个目标模式。定理 1.1 的特定形状则只依赖 $k,s$，不随总乘积目标深度 $R$ 变化。

## 5. 适用范围

(1.1) 固定的是单项式的 $F_3$ 值，而不是整数本身或单项式的数值。各素数端点互异；当 $X>3$ 时，步长也不同于端点：$i>0$ 时 $p_i>d$，而 $d=n$ 会使 $p_1=n(1+h_1)$ 为合数。

所有阶数、目标深度、模数和偏移均先固定。不据此推断阶数或精度随 $X$ 增长时的统一相对误差，不将有限同余比例当作任意素数抽样的独立性假设。

实际间距为 $h_i d$，其中 $d$ 可变。固定 $d$ 后，剩余一变量形式的线性部分成比例，(LF) 不再适用。本文不包含固定间距孪生素数存在性结论。

## 参考

[1] B. Green and T. Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850, Main Theorem and Corollary 1.7.
https://annals.math.princeton.edu/2010/171-3/p08

[2] B. Green and T. Tao, *The Möbius function is strongly orthogonal to nilsequences*, Annals of Mathematics 175 (2012), 541–566.
https://annals.math.princeton.edu/2012/175-2/p03

[3] B. Green, T. Tao and T. Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm*, Annals of Mathematics 176 (2012), 1231–1372; corrected preprint arXiv:1009.3998v5 and the authors' erratum.
https://arxiv.org/abs/1009.3998v5

有限复杂度线性形式定理是外部输入。幂赋值、有限根计数、局部因子和低次数刚性均在正文中证明；有限数值核验不作为这些定理的证明。

# F3D-MULTI：完整书面证明

状态分项：MULTI-1/2、MULTI-3 构造方向、有限热带表达式 Lipschitz 界与固定幅度开关保留 `PAPER-AUDITED`；MULTI-3 必要性及其所支撑的 MULTI-4 全体可实现函数结论为 `RESEARCH`（审计缺口）。2026-09-30 修正 `F3D-CORR-MULTI-L12` 见 §9 和 [修正报告](../../../../reports/f3d_proof_boundary_corrections.md)。精确范围见 [theorem.md](theorem.md)。

## 1. 和差比坐标

对每个输入
\[
X_i=(n_i,d_i)\in\mathcal D
\]
令
\[
u_i=n_i+d_i,\qquad
v_i=n_i-d_i,
\qquad
x_i=\frac{u_i}{v_i}\in\mathbb Q^\times.
\]
则
\[
\boxed{
F(X_i)=v_3(x_i).
}
\tag{1.1}
\]

反过来，任意
\[
x_i=a_i/b_i\in\mathbb Q^\times
\]
都可由整数输入
\[
n_i=a_i+b_i,\qquad
d_i=a_i-b_i
\]
实现。因为
\[
n_i+d_i=2a_i,\qquad
n_i-d_i=2b_i
\]
且 \(v_3(2)=0\)。

因此多输入问题可在
\[
(\mathbb Q^\times)^m
\]
上研究固定有理函数如何改变赋值向量
\[
\mathbf t=(v_3(x_1),\ldots,v_3(x_m)).
\]

---

## 2. 二次正性检测

定义
\[
\Theta(n,d)
=
\left(
3n^2-2nd+3d^2,\,
(n-d)^2
\right).
\]
写
\[
u=n+d,\qquad v=n-d.
\]
直接展开：
\[
3n^2-2nd+3d^2=u^2+2v^2,
\]
\[
(n-d)^2=v^2.
\]
因此若输出记为
\[
(N,D)=\Theta(n,d),
\]
则
\[
N+D=u^2+3v^2,
\qquad
N-D=u^2+v^2.
\tag{2.1}
\]

令
\[
a=v_3(u),\qquad b=v_3(v).
\]

### 2.1 第一侧

两项
\[
u^2,\qquad 3v^2
\]
的赋值分别是
\[
2a,\qquad1+2b.
\]
一个偶、一个奇，永不相等，所以最低项唯一：
\[
\boxed{
v_3(u^2+3v^2)=\min(2a,1+2b).
}
\tag{2.2}
\]

### 2.2 第二侧

若 \(a\ne b\)，
\[
u^2+v^2
\]
的最低赋值项唯一；若 \(a=b\)，约去共同因子后两个单位平方模 \(3\) 都为 \(1\)，其和模 \(3\) 为 \(2\)。故统一有
\[
\boxed{
v_3(u^2+v^2)=2\min(a,b).
}
\tag{2.3}
\]

所以
\[
F(\Theta(n,d))
=
\min(2a,1+2b)-2\min(a,b).
\]
若 \(a\le b\)，右侧为 \(0\)；若 \(a>b\)，因为 \(a\ge b+1\)，
\[
\min(2a,1+2b)=1+2b
\]
而
\[
2\min(a,b)=2b,
\]
故输出为 \(1\)。

因此
\[
\boxed{
F(\Theta(n,d))
=
\mathbf1_{\{F(n,d)>0\}}.
}
\tag{2.4}
\]

又
\[
D=v^2>0,
\qquad
N-D=u^2+v^2>0,
\]
所以
\[
N>D>0.
\]

---

## 3. 两输入最小值与最大值

对非零有理数 \(x,y\)，定义
\[
\mu(x,y)
=
\frac{x^3+3y^3}{x^2+3y^2}.
\]
先说明分子分母均不为零。

若
\[
x^2+3y^2=0,
\]
则
\[
(x/y)^2=-3,
\]
在 \(\mathbb Q\) 中不可能。

若
\[
x^3+3y^3=0,
\]
则
\[
(x/y)^3=-3,
\]
也无有理解。

令
\[
a=v_3(x),\qquad b=v_3(y).
\]
分子两项的赋值为
\[
3a,\qquad1+3b,
\]
分母两项为
\[
2a,\qquad1+2b.
\]
由于一边模 \(3\) 或模 \(2\) 的奇偶偏移不同，各自的两个候选赋值永不相等，所以没有最低项抵消：
\[
v_3(x^3+3y^3)=\min(3a,1+3b),
\]
\[
v_3(x^2+3y^2)=\min(2a,1+2b).
\]

若 \(a\le b\)，
\[
3a<1+3b,\qquad2a<1+2b,
\]
所以
\[
v_3(\mu)=3a-2a=a.
\]

若 \(a>b\)，则 \(a\ge b+1\)，于是
\[
1+3b<3a,\qquad1+2b<2a,
\]
故
\[
v_3(\mu)=(1+3b)-(1+2b)=b.
\]

因此
\[
\boxed{
v_3(\mu(x,y))
=
\min(a,b).
}
\tag{3.1}
\]

又
\[
v_3(xy)=a+b,
\]
所以
\[
\boxed{
v_3\!\left(\frac{xy}{\mu(x,y)}\right)
=
a+b-\min(a,b)
=
\max(a,b).
}
\tag{3.2}
\]

### 3.1 回到整数多项式对

若某个固定有理函数
\[
R(x_1,\ldots,x_m)=A/B
\]
在
\[
(\mathbb Q^\times)^m
\]
上无零点和极点，则代入
\[
x_i=u_i/v_i
\]
后取共同多重齐次化次数，得到整数或有理系数多项式
\[
\widetilde A(\mathbf u,\mathbf v),
\qquad
\widetilde B(\mathbf u,\mathbf v)
\]
且二者在定义域上不为零。

清去系数分母后，定义
\[
P=L(\widetilde A+\widetilde B),
\qquad
Q=L(\widetilde A-\widetilde B).
\]
则
\[
P+Q=2L\widetilde A,\qquad
P-Q=2L\widetilde B,
\]
所以输出仍在定义域，并且
\[
F(P,Q)=v_3(R(x_1,\ldots,x_m)).
\tag{3.3}
\]

因此 (3.1)、(3.2) 直接给出固定整数多项式对实现
\[
\min(t_1,t_2),
\qquad
\max(t_1,t_2).
\]

---

## 4. 批量最小值与第一极小位置

固定 \(m\ge1\)，取
\[
x_0,\ldots,x_{m-1}\in\mathbb Q^\times.
\]
对 \(k\ge m\) 定义
\[
H_k=\sum_{i=0}^{m-1}3^i x_i^k.
\]

令
\[
a_i=v_3(x_i),
\qquad
a=\min_i a_i,
\]
以及
\[
i_0=\min\{i:a_i=a\}.
\]

第 \(i\) 项
\[
3^i x_i^k
\]
的赋值为
\[
ka_i+i.
\tag{4.1}
\]

若 \(a_i=a\) 且 \(i>i_0\)，则
\[
ka_i+i-(ka+i_0)=i-i_0>0.
\]

若 \(a_i\ge a+1\)，则
\[
ka_i+i-(ka+i_0)
\ge
k+i-i_0.
\]
因为
\[
k\ge m,\qquad
0\le i,i_0\le m-1,
\]
有
\[
k+i-i_0
\ge
m-(m-1)=1.
\]
所以 \(i_0\) 对应项具有严格唯一的最小赋值。

因此
\[
\boxed{
v_3(H_k)=ka+i_0.
}
\tag{4.2}
\]

相邻两次幂给出
\[
v_3(H_{m+1})=(m+1)a+i_0,
\]
\[
v_3(H_m)=ma+i_0.
\]
相减：
\[
\boxed{
v_3(H_{m+1}/H_m)=a.
}
\tag{4.3}
\]

另一方面
\[
v_3(H_m^{m+1})
=
(m+1)(ma+i_0),
\]
\[
v_3(H_{m+1}^{m})
=
m((m+1)a+i_0).
\]
相减得到
\[
\boxed{
v_3\!\left(
\frac{H_m^{m+1}}{H_{m+1}^{m}}
\right)
=
i_0.
}
\tag{4.4}
\]

由于每个 \(H_k\) 都有唯一最低项，所以
\[
H_k\ne0.
\]
于是这些有理函数全域有效，并可按第 3.1 节转成整数多项式对。

---

## 5. 有限整数热带表达式的标准形

称
\[
T(\mathbf t)=
\min_{a}
(c_a+\mathbf u_a\cdot\mathbf t)
\]
为整数热带多项式。

### 引理 5.1

由整数常数、坐标、加、减、\(\min\)、\(\max\) 有限复合得到的每个函数，都可以写成
\[
\boxed{
g=T_1-T_2
}
\tag{5.1}
\]
其中 \(T_1,T_2\) 为整数热带多项式。

### 证明

整数仿射函数本身可视为只有一个项的热带多项式。

若
\[
f=A-B,\qquad
g=C-D
\]
其中 \(A,B,C,D\) 都是热带多项式，则
\[
f+g=(A+C)-(B+D),
\]
而两个热带多项式之和仍是热带多项式，因为
\[
\min_i a_i+\min_j c_j
=
\min_{i,j}(a_i+c_j).
\]

同理
\[
f-g=(A+D)-(B+C).
\]

再看最小值：
\[
\min(f,g)
=
\min(A-B,C-D).
\]
加上共同项 \(B+D\)：
\[
\min(f,g)+(B+D)
=
\min(A+D,C+B).
\]
所以
\[
\boxed{
\min(f,g)
=
\min(A+D,C+B)-(B+D).
}
\]
右侧仍为两个热带多项式之差。

最大值用
\[
\max(f,g)=-\min(-f,-g)
\]
处理。

归纳即得。 \(\square\)

反向显然：式 (5.1) 本身由允许的有限操作构成。

所以 theorem.md 中的两个定义等价。

---

## 6. 分类定理：构造方向

设
\[
g:\mathbb Z^m\to\mathbb Z
\]
是有限整数热带表达式。

在有理坐标中，基本操作对应：

\[
t_i+t_j
\longleftrightarrow
x_ix_j,
\]
\[
t_i-t_j
\longleftrightarrow
x_i/x_j,
\]
\[
\min(t_i,t_j)
\longleftrightarrow
\mu(x_i,x_j),
\]
\[
\max(t_i,t_j)
\longleftrightarrow
\frac{x_ix_j}{\mu(x_i,x_j)},
\]
\[
r
\longleftrightarrow
3^r.
\]

当 \(r<0\) 时常数 \(3^r\) 是有理数，这没有问题：在最终统一清系数分母时会回到整数多项式。

所有基本有理函数在
\[
(\mathbb Q^\times)^m
\]
上均非零且有限。有限次乘法、除法和代入后仍然没有零点或极点。

因此得到固定有理函数
\[
R_g(x_1,\ldots,x_m)
\]
满足
\[
v_3(R_g(\mathbf x))
=
g(v_3(x_1),\ldots,v_3(x_m)).
\]
第 3.1 节的清分母、多重齐次化与和差回代给出全域有效的整数多项式对。

故所有有限整数热带表达式都可实现。

---

## 7. 分类定理：必要性的输入网格

现在设一个固定整数多项式对
\[
(P,Q)
\]
全域实现
\[
g:\mathbb Z^m\to\mathbb Z.
\]
令
\[
A=P+Q,\qquad B=P-Q.
\]
由于输出始终在 \(\mathcal D\)，
\[
A\ne0,\qquad B\ne0
\]
对所有合法整数输入成立。

把每个输入换成和差变量：
\[
u_i=n_i+d_i,\qquad
v_i=n_i-d_i.
\]
因为
\[
n_i=(u_i+v_i)/2,\qquad
d_i=(u_i-v_i)/2,
\]
乘上固定的 \(2^D\) 后，可把 \(A,B\) 视为
\[
2m
\]
个整数变量
\[
u_1,v_1,\ldots,u_m,v_m
\]
上的整数多项式；乘以 \(2^D\) 不改变三进赋值。

设总次数均不超过 \(D\)。

固定
\[
\mathbf t=(t_1,\ldots,t_m)\in\mathbb Z^m.
\]
写
\[
t_i^+=\max(t_i,0),
\qquad
t_i^-=\max(-t_i,0).
\]
对单位参数
\[
s_i,r_i\in\mathbb Z,\qquad3\nmid s_ir_i
\]
取
\[
u_i=2\cdot3^{t_i^+}s_i,
\qquad
v_i=2\cdot3^{t_i^-}r_i.
\tag{7.1}
\]
则
\[
v_3(u_i)-v_3(v_i)=t_i,
\]
而
\[
n_i=(u_i+v_i)/2,\qquad
d_i=(u_i-v_i)/2
\]
是整数且
\[
(n_i,d_i)\in\mathcal D.
\]

因此，对所有单位选择 \(\mathbf s,\mathbf r\)，
\[
v_3(A(\mathbf t;\mathbf s,\mathbf r))
-
v_3(B(\mathbf t;\mathbf s,\mathbf r))
=
g(\mathbf t).
\tag{7.2}
\]

---

## 8. 有限单位网格插值界

令
\[
S_D=\{1,4,7,\ldots,1+3D\}.
\]
它有 \(D+1\) 个三进单位。

### 引理 8.1

设
\[
C(Y_1,\ldots,Y_\ell)\in\mathbb Z[Y_1,\ldots,Y_\ell]
\]
非零，并且每个变量次数不超过 \(D\)。

令
\[
\tau(C)
=
\min_\alpha v_3(c_\alpha)
\]
为最低系数赋值，并令
\[
\eta(C)
=
\min_{\mathbf y\in S_D^\ell}
v_3(C(\mathbf y)).
\]
则
\[
\boxed{
0\le
\eta(C)-\tau(C)
\le
\ell\bigl(D+v_3(D!)\bigr).
}
\tag{8.1}
\]

### 证明

下界来自非阿基米德不等式：
\[
v_3(C(\mathbf y))\ge\tau(C)
\]
因为所有 \(y_i\) 都是单位。

上界用张量积 Lagrange 插值。

一变量节点
\[
y_j=1+3j,
\qquad
0\le j\le D.
\]
第 \(j\) 个 Lagrange 基函数分母为
\[
\prod_{h\ne j}(y_j-y_h)
=
3^D
\prod_{h\ne j}(j-h).
\]
所以其三进赋值为
\[
D+v_3(j!)+v_3((D-j)!)
\le
D+v_3(D!).
\tag{8.2}
\]

对 \(\ell\) 个变量张量插值，恢复任意系数时，分母赋值至多
\[
\ell(D+v_3(D!)).
\tag{8.3}
\]

若所有网格值都满足
\[
v_3(C(\mathbf y))
>
\tau(C)+\ell(D+v_3(D!)),
\]
则插值表达会迫使所有系数的赋值都严格大于 \(\tau(C)\)，与其定义矛盾。

因此至少有一个网格点满足 (8.1)。 \(\square\)

---

## 9. 固定网格值的赋值是有限分段整数仿射函数

固定一个单位网格点
\[
\omega=(\mathbf s,\mathbf r)\in S_D^{2m}.
\]
代入 (7.1) 后，任意单项
\[
c_\alpha
\prod_i u_i^{a_i}v_i^{b_i}
\]
的三进赋值为
\[
v_3(c_\alpha)
+
\sum_i a_i t_i^+
+
\sum_i b_i t_i^-.
\tag{9.1}
\]
因为
\[
t_i^+=\max(t_i,0),
\qquad
t_i^-=\max(-t_i,0),
\]
(9.1) 本身是有限整数热带表达式。

### 引理 9.1（有限分区部分保留，热带等价断言撤回）

对固定网格点 \(\omega\)，函数
\[
\mathbf t
\longmapsto
v_3(A(\mathbf t;\omega))
\]
原有限分区断言为：它是有限整数仿射分区上的整数仿射函数。下面保留该部分原论证；本次反例不否定这个允许不连续的分区性质，也不重新认证它。原文续称“等价地，它是有限整数热带表达式”，该等价断言错误，现撤回。

### 原有限分区论证（不能据此推出热带表示）

\(A(\mathbf t;\omega)\) 是有限项之和。每项的赋值由 (9.1) 给出。

先按这些有限整数分段仿射函数的全序关系划分 \(\mathbb Z^m\)。在每个格点胞腔上，哪些项取得最小赋值是固定的。

若最低项唯一，和的赋值就是该最低值。

若最低项并列，提取共同的
\[
3^{L(\mathbf t)}.
\]
并列最低项除去该幂后的单位系数只由固定网格点 \(\omega\) 和原多项式系数决定，不再依赖 \(\mathbf t\)。

- 若这些单位项之和非零，记其固定赋值为 \(c\)。那么它们整体贡献候选
  \[
  L(\mathbf t)+c.
  \]
- 若完全抵消，则把该组删去。

剩余非最低项相对 \(L(\mathbf t)\) 的赋值差仍来自有限整数仿射函数。比较
\[
L(\mathbf t)+c
\]
与下一批候选，再细分胞腔。

每次若发生完全抵消，项数严格减少；若不完全抵消，则产生一个固定整数修正。原项数有限，所以递归有限终止。

由于全域输出要求 \(A\) 在所有这些合法网格输入上非零，不会出现最终值 \(+\infty\)。

因此得到有限整数仿射分区。 \(\square\)

同理适用于 \(B\)。

> 引理 8.1 控制的是网格最小值与最低系数赋值之差，不是每个固定网格值的抵消深度；它不能直接补足上述热带等价断言。

### 9.2 热带等价断言的反例：F3D-CORR-MULTI-L12

取三个输入，令
\[
C=(u_1-u_2)^2+3u_3^2,\qquad P=C,\qquad Q=0.
\]
合法输入有 \(u_3=n_3+d_3\ne0\)，故整数域上 \(C>0\)。于是
\[
A=P+Q=C=P-Q=B\ne0,
\]
输出始终在 \(\mathcal D\)，并全域实现 \(g=0\)。定义域允许第二坐标为零；没有利用奇异输入或奇异输出。

取次数上界 \(D=2\) 及固定单位 \(s_i=r_i=1\in S_2=\{1,4,7\}\)。在非负整数向量上，(7.1) 给出
\[
n_i=3^{t_i}+1,\qquad d_i=3^{t_i}-1,
\]
所以每个输入合法且 \(F(X_i)=t_i\)。该固定网格的赋值函数为
\[
h(\mathbf t)=v_3\!\left(4\bigl((3^{t_1}-3^{t_2})^2+3^{2t_3+1}\bigr)\right).
\]
对每个整数 \(M\ge0\)，直接计算得
\[
h(0,0,M)=2M+1,\qquad h(1,0,M)=0.
\]
第二个等式因为 \(4+3^{2M+1}\equiv1\pmod3\)。两点的上确界距离为 \(1\)，跳幅 \(2M+1\) 无界。

每个有限整数仿射函数有有限全局 Lipschitz 常数；有限次加减使常数相加，min/max 使常数取最大。因此每个有限整数热带表达式都有有限全局 Lipschitz 常数（亦见 §12）。上面的 \(h\) 不可能是这样的表达式。

这只反驳引理 9.1 的热带等价断言及 §10 对它的使用。它不反驳允许不连续的有限仿射分区性质，更不反驳主分类：此处 \(A=B\)，最终输出 \(g=0\) 的跳幅完全相消。

---

## 10. 网格最小值直接恢复 \(g\)

定义有限网格
\[
\Omega=S_D^{2m}.
\]
令
\[
\eta_A(\mathbf t)
=
\min_{\omega\in\Omega}
v_3(A(\mathbf t;\omega)),
\]
\[
\eta_B(\mathbf t)
=
\min_{\omega\in\Omega}
v_3(B(\mathbf t;\omega)).
\]

由 (7.2)，对每个固定 \(\omega\)
\[
v_3(A(\mathbf t;\omega))
=
v_3(B(\mathbf t;\omega))
+
g(\mathbf t).
\]
因为 \(g(\mathbf t)\) 与 \(\omega\) 无关，对有限网格取最小值得
\[
\boxed{
\eta_A(\mathbf t)
=
\eta_B(\mathbf t)+g(\mathbf t).
}
\tag{10.1}
\]
所以
\[
\boxed{
g(\mathbf t)
=
\eta_A(\mathbf t)-\eta_B(\mathbf t).
}
\tag{10.2}
\]

恒等式 (10.1)、(10.2) 仍成立，且不需要引理 9.1 的热带断言。原文接着用“每个固定网格值都是有限整数热带表达式”推出 \(\eta_A,\eta_B\) 及 \(g\) 都是热带表达式；§9.2 已反驳该前提。因此这一步及“必要性得证”撤回。

是否可直接用网格最小值和插值界修复表示性，是待证明问题。这里不以修复设想替代证明，MULTI-3 必要性保持 `RESEARCH`。

---

## 11. 与“有界抵消修正”版本的关系

研究稿中可先定义“朴素热带化”
\[
\tau_A(\mathbf t)
=
\min_\alpha
\left(
v_3(c_\alpha)
+
\sum_i a_i t_i^+
+
\sum_i b_i t_i^-
\right).
\]
引理 8.1 对单位网格代入给出
\[
0\le
\eta_A(\mathbf t)-\tau_A(\mathbf t)
\le
2m\bigl(D+v_3(D!)\bigr).
\tag{11.1}
\]
同理对 \(B\)。

于是
\[
g(\mathbf t)
=
\bigl(\tau_A-\tau_B\bigr)
+
\delta(\mathbf t),
\]
其中
\[
|\delta(\mathbf t)|
\le
4m\bigl(D+v_3(D!)\bigr).
\]
这就是研究稿中的“有限热带主部 + 有界抵消修正”。

有界修正的这些估计不能自动提供有限热带表示。原文声称第 9–10 节已证明 \(\eta_A,\eta_B\) 是热带表达式并闭合必要性；该结论现因 §9.2 的反例撤回。修复需要另外的表示性论证。

---

## 12. 统一 Lipschitz 边界

任意整数仿射函数
\[
L(\mathbf t)=c+\mathbf a\cdot\mathbf t
\]
满足
\[
|L(\mathbf t)-L(\mathbf s)|
\le
\|\mathbf a\|_1
\|\mathbf t-\mathbf s\|_\infty.
\]
有限个 \(L_i\) 的
\[
\min_i L_i
\]
与
\[
\max_i L_i
\]
具有 Lipschitz 常数
\[
\max_i\|\mathbf a_i\|_1.
\]

有限次加、减只会把常数相加。

因此每个有限整数热带表达式 \(g\) 都存在
\[
L<\infty
\]
使
\[
\boxed{
|g(\mathbf t)-g(\mathbf s)|
\le
L\|\mathbf t-\mathbf s\|_\infty.
}
\tag{12.1}
\]

以上只确立有限整数热带表达式的 Lipschitz 界。原文借分类必要性将其推广到每个固定多项式可实现函数；该推广的当前证明路线有 §9.2 所示缺口，保留为 `RESEARCH`，不再标记审计通过。

---

## 13. 无界条件开关：非热带性与待修复的不可实现路线

本节距离计算仍证明该开关不是有限整数热带表达式。若要据此推出多项式不可实现，仍需修复分类必要性；该后半结论为 `RESEARCH`。

定义
\[
G(t,s)
=
\begin{cases}
s,&t\ge0,\\
0,&t<0.
\end{cases}
\]
若它是有限整数热带表达式，则由 (12.1) 存在固定 \(L\) 使
\[
|G(t,s)-G(t',s')|
\le
L\max(|t-t'|,|s-s'|).
\]

但对任意正整数 \(M\)，
\[
G(0,M)=M,
\qquad
G(-1,M)=0.
\]
输入距离为
\[
\max(1,0)=1,
\]
输出差为
\[
M.
\]
取 \(M>L\) 即矛盾。

所以
\[
\boxed{
G\text{ 不是有限整数热带表达式}.
}
\tag{13.1}
\]

原文进一步宣称“不可由全域固定整数多项式对实现”；当前路线缺少从可实现性到热带性的必要性论证，故暂不把该更强结论作为已审计结果。

---

## 14. 固定幅度开关可以实现

由第 2 节或单输入分类，可实现
\[
H(t)=\mathbf1_{\{t\ge0\}}.
\]
在整数格点上显式写成
\[
\boxed{
H(t)=\min(1,\max(0,t+1)).
}
\tag{14.1}
\]

定义
\[
s_+=\max(s,0),
\qquad
(-s)_+=\max(-s,0).
\]
对固定 \(B\ge0\)，令
\[
\boxed{
G_B(t,s)
=
\min(s_+,BH(t))
-
\min((-s)_+,BH(t)).
}
\tag{14.2}
\]

若 \(t<0\)，
\[
H(t)=0
\]
所以
\[
G_B=0.
\]

若 \(t\ge0\)，
\[
H(t)=1
\]
于是
\[
G_B
=
\min(s_+,B)-\min((-s)_+,B)
=
\max(-B,\min(s,B)).
\]

所以固定幅度条件选择属于可实现类。

---

## 15. 第一极小位置为什么不违背 Lipschitz 边界

批量构造输出
\[
i_0\in\{0,1,\ldots,m-1\}.
\]
对固定输入数 \(m\)，这是统一有界的离散输出。

因此即使 \(i_0\) 会随输入赋值向量跳变，其跳变量至多 \(m-1\)，与 Lipschitz 性并不矛盾；该构造不依赖分类必要性。

无界开关的非热带性来自条件边界两侧无界的输出差；从这里到多项式不可实现的当前路线仍待修复。

---

## 16. 任意素数 \(p\) 的最小值公式

令 \(p\) 为任意素数。定义
\[
\mu_p(x,y)
=
\frac{x^3+py^3}{x^2+py^2}.
\]
分母若为零会给出
\[
(x/y)^2=-p,
\]
不可能由非零有理数实现；分子为零会给出
\[
(x/y)^3=-p,
\]
同样不可能。

令
\[
a=v_p(x),\qquad b=v_p(y).
\]
候选赋值为
\[
3a,\ 1+3b
\]
以及
\[
2a,\ 1+2b,
\]
仍永不相等。

与第 3 节完全相同的分情况得到
\[
\boxed{
v_p(\mu_p(x,y))
=
\min(v_p(x),v_p(y)).
}
\tag{16.1}
\]

批量公式中把
\[
3^i
\]
改成
\[
p^i
\]
也保持唯一最低项证明。

所以这套固定多项式表达能力的 min/max 骨架并不依赖 \(p=3\)。

---

## 17. 文献边界

有限 min/max 与仿射函数生成的分段线性函数、以及 tropical rational function 的差分表示已有独立研究。Tran–Wang 研究 tropical rational functions 的最小表示复杂度；Koutschan–Moser–Ponomarchuk–Schicho 研究连续分段线性函数的 max/min 型表示。

本文不声称一般热带表示理论新颖。

本文原拟确立下面这个算术等价；当前仅构造方向保留，必要性为 `RESEARCH`：

> 固定整数多项式对在全部整数输入上，只通过 \(F_{3,D}\) 值观察输入时，其精确表达能力恰好等于有限整数热带表达式在 \(\mathbb Z^m\) 上的限制。

该“全域算术可实现性等价”是否已有完全相同表述，尚未完成系统文献查新。

---

## 18. 有限 sanity check

研究轮报告：

- 复跑上一轮 211,072 项检查；
- 新增 78,440 项精确算术检查；
- 覆盖二次正性检测；
- 双输入最小/最大；
- 批量最小值与第一极小位置；
- 有限表达式提升；
- 抵消合并与插值界实例。

这些历史计算只用于排错，不修复 §9.2 所指出的必要性缺口，也不证明一般不可实现性。2026-09-30 的反例有限回归见 `scripts/check_f3d_proof_boundaries.py` 与 `reports/f3d_proof_boundary_check.json`；一般的无界跳幅由 §9.2 的全参数计算说明，不由有限样本或 Lean 内核验证。

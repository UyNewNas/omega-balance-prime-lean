# F3-WAV：完整书面证明

来源状态：\`PAPER-AUDITED\`（固定提交 `311b0a226c0a64854f495dd3d1561fefaf6cb6e6`）。
本次仅修正第 1 节的非整除论证并明确继承定义域；其余证明沿用来源，未在本次重新审计。
Lean 候选只覆盖该局部非整除步骤，尚待精确 head CI。

## 1. 条件传递

一般传递取整数 \(h\)、自然数 \(r\ge1\)，短窗口另要求 \(r\ge2\)。

设
\[
P_h(n)=n(n+h)+1,\qquad
Q=3^{2r},\qquad m=3^r.
\]
对固定 \(a\bmod m\)，写
\[
n=a+mb.
\]
模 \(Q\) 有
\[
P_h(a+mb)
\equiv
P_h(a)+m(2a+h)b.
\tag{1.1}
\]

若
\[
m\mid 2a+h,
\]
则线性项恒为零。又
\[
4P_h(a)=(2a+h)^2-(h^2-4),
\]
而 \(4\) 是三进单位，所以在临界类上
\[
W_r(P_h(a))=W_r(D_h).
\]
因此整个块贡献
\[
mW_r(D_h).
\]

若
\[
t=v_3(2a+h)<r,
\]
则随着 \(b\bmod m\) 变化，
\[
m(2a+h)b
\]
遍历模 \(Q\) 下所有 \(3^{r+t}\) 的倍数，每个值重复 \(3^t\) 次。

若
\[
3^{r+t}\nmid P_h(a),
\]
则 \(Q\mid P_h(a+mb)\) 与 \(Q/3\mid P_h(a+mb)\) 都无解。

若
\[
3^{r+t}\mid P_h(a),
\]
则：
- \(Q\mid P_h\) 有 \(3^t\) 个 \(b\)；
- \(Q/3\mid P_h\) 有 \(3^{t+1}\) 个 \(b\)。

于是该块的差分权和为
\[
3\cdot3^t-3^{t+1}=0.
\]

这证明
\[
\sum_{b=0}^{m-1}w_{r,h}(a+mb)
=
mW_r(D_h)\mathbf1_{2a+h\equiv0\pmod m}.
\]

乘上任意只依赖 \(a=n\bmod m\) 的函数 \(B(a)\) 后再对 \(a\) 求和，得到带 \(B\) 的条件传递公式。

在 \(r\ge2\)、整数
\[
2<h<3^{2r-1}-2
\]
时，令 \(q=3^{2r-1}\)。分解
\[
D_h=(h-2)(h+2),\qquad 0<h-2<h+2<q.
\]
两因子之差为 \(4\)，而 \(3\nmid4\)，所以 \(3\) 不可能同时整除两因子。
若 \(q\mid D_h\)，素数幂整除乘积且一因子不被 \(3\) 整除，便迫使 \(q\)
整除另一因子；该因子严格介于 \(0\) 和 \(q\) 之间，矛盾。因此
\[
3^{2r-1}\nmid D_h.
\]
又 \(3^{2r-1}\mid3^{2r}\)，故 \(3^{2r}\nmid D_h\)，两个整除指标都为零，得到
\[
W_r(D_h)=0.
\]
这里 \(D_h>0\)，也可表述为 \(v_3(D_h)<2r-1\)。不需要、也不能声称
\(D_h<q\)：例如 \(r=2,h=10,H=10\) 满足原短窗口，但 \(D_h=96>27=q\)。
严格上界不能改为非严格：第一个排除点 \(h=q-2\) 有
\(D_h=q(q-4)\)，\(3\nmid q-4\)，故 \(v_3(D_h)=2r-1\)、\(W_r(D_h)=-1\)。
而 \(h=2\) 时
\[
P_2(n)=(n+1)^2,
\]
所以
\[
Q\mid P_2(n)\iff3^r\mid n+1,
\]
而
\[
Q/3\mid P_2(n)
\]
在平方赋值下与同一条件等价，于是
\[
w_{r,2}(n)=2\mathbf1_{n\equiv-1\pmod m}.
\]

## 2. 两小波分解

设
\[
D_h=h^2-4,\qquad t=v_3(D_h)<2r-1.
\]
完成平方：
\[
4P_h(n)=(2n+h)^2-D_h.
\]
因为 \(4\) 是三进单位，高层整除等价于
\[
(2n+h)^2\equiv D_h\pmod{3^R}.
\]

若 \(t\) 为奇数，则一个平方的赋值不能等于 \(t\)，无高层根。

若
\[
t=2s
\]
但单位部分
\[
D_h/3^{2s}\equiv2\pmod3,
\]
也没有单位平方根，因为模 \(3\) 的非零平方只有 \(1\)。

剩余情形：
\[
D_h=3^{2s}u,\qquad u\equiv1\pmod3.
\]
\(u\) 有两个单位平方根，并因导数 \(2y\) 为单位而逐层唯一提升。于是得到两个三进根
\[
\beta_\pm
\]
满足
\[
\beta_\pm^2=D_h,
\qquad
v_3(\beta_+-\beta_-)=s.
\]
转回 \(n\) 坐标得到
\[
\alpha_\pm=\frac{\beta_\pm-h}{2}.
\]

因
\[
P_h(n)=(n-\alpha_+)(n-\alpha_-),
\]
对 \(R>2s\)，两个根邻域互不相交，且
\[
v_3(P_h(n))\ge R
\]
当且仅当
\[
n\equiv\alpha_+\pmod{3^{R-s}}
\quad\text{或}\quad
n\equiv\alpha_-\pmod{3^{R-s}}.
\]

取 \(R=2r\) 与 \(R=2r-1\)，并令
\[
L=2r-s,
\]
便得到
\[
w_{r,h}(n)
=
\sum_{\sigma=\pm}
\left(
3\mathbf1_{n\equiv\alpha_\sigma\pmod{3^L}}
-
\mathbf1_{n\equiv\alpha_\sigma\pmod{3^{L-1}}}
\right).
\]

每个父类模 \(3^{L-1}\) 含三个子类；指定子类权为
\[
3-1=2,
\]
其余两个子类权为
\[
-1.
\]
所以是 \((2,-1,-1)\)。

两个父类不相交，因为
\[
v_3(\alpha_+-\alpha_-)=s<L-1.
\]

## 3. Fourier 与能量

在模
\[
M=3^L
\]
上令
\[
\psi_{L,a}(n)
=
3\mathbf1_{n\equiv a\pmod M}
-
\mathbf1_{n\equiv a\pmod{M/3}}.
\]
归一化 Fourier 系数直接计算：

第一项贡献
\[
\frac3M e_M(-\xi a).
\]
第二项是三个子类之和，其 Fourier 只在
\[
3\mid\xi
\]
时保留，并恰好抵消第一项对应部分。

于是
\[
\widehat\psi(\xi)
=
\begin{cases}
\dfrac3M e_M(-\xi a),&3\nmid\xi,\\
0,&3\mid\xi.
\end{cases}
\]

对单个父类，三个子类值是
\[
2,-1,-1,
\]
平方和为
\[
4+1+1=6.
\]
两个父类不交，所以
\[
\sum_{n\bmod M}w_{r,h}(n)^2=12.
\]

## 4. 单位公差等差数列常数界

考虑单个
\[
\psi_{L,a}(a_0+dj),
\qquad3\nmid d.
\]
模 \(3^{L-1}\) 的父类在 \(j\) 中仍是一个等差类；每连续三个命中父类的 \(j\) 中，三个细子类各出现一次。

若某个连续指标区间中父类命中数为
\[
N=3q+t,\qquad t\in\{0,1,2\},
\]
则指定子类命中数为 \(q\) 或 \(q+1\)。因此
\[
|3N_{\rm child}-N_{\rm parent}|\le2.
\]
每个小波贡献绝对值至多 \(2\)，两个小波合计至多
\[
4.
\]

这证明
\[
\left|
\sum_{j\in J}w_{r,h}(a+dj)
\right|\le4.
\]

## 5. 有限除数和传递

展开
\[
A(n)B(n+h)
=
\sum_{d\mid n}\sum_{e\mid n+h}a_db_e.
\]
固定 \(d,e\)。

联立
\[
n\equiv0\pmod d,\qquad
n\equiv-h\pmod e
\]
可解当且仅当
\[
\gcd(d,e)\mid h.
\]
可解时解集是一条公差
\[
\operatorname{lcm}(d,e)
\]
的等差数列。因为 \(3\nmid de\)，该公差是三进单位。

当 \(h>2\) 时，第 4 节直接给每对 \((d,e)\) 的贡献绝对值至多 \(4\)，于是
\[
|\mathcal E_h|
\le
4\sum_d|a_d|\sum_e|b_e|
=
4UV.
\]

当 \(h=2\) 时
\[
w_{r,2}(n)=2\mathbf1_{n\equiv-1\pmod{3^r}}.
\]
若 \(\gcd(d,e)\mid2\)，再与
\[
n\equiv-1\pmod{3^r}
\]
用 CRT 合并，因为 \(3\nmid de\)，得到模
\[
3^r\operatorname{lcm}(d,e)
\]
的唯一类。因此区间 \([1,X]\) 中点数为
\[
\frac{X}{3^r\operatorname{lcm}(d,e)}+O(1).
\]
乘权 \(2\)，求和后得到主项与误差
\[
|\mathcal E_2|\le2UV.
\]

## 6. 一个端点为素数

\(h=2\) 时
\[
\sum_{3<p\le X}w_{r,2}(p)
=
2\pi(X;3^r,-1)+O(1).
\]
等差数列素数定理给
\[
\pi(X;3^r,-1)
\sim
\frac{\operatorname{Li}(X)}{\varphi(3^r)}.
\]
因此除以
\[
\pi(X)\sim\operatorname{Li}(X)
\]
得到极限
\[
\frac2{\varphi(3^r)}
=
\frac2{2\cdot3^{r-1}}
=
3^{1-r}.
\]

对 \(h>2\) 的非零情形，由两小波分解，每个小波只涉及：
- 一个模 \(3^L\) 的单位类，系数 \(3\)；
- 一个模 \(3^{L-1}\) 的父类，系数 \(-1\)。

等差数列素数定理给出的主项为
\[
3\frac{\operatorname{Li}(X)}{\varphi(3^L)}
-
\frac{\operatorname{Li}(X)}{\varphi(3^{L-1})}.
\]
而
\[
\varphi(3^L)=3\varphi(3^{L-1}),
\]
故主项精确抵消。

对两个根求和仍为 \(0\)。

若模数满足
\[
Q\le(\log X)^B,
\]
使用 Siegel–Walfisz 的一致余项，即得 theorem.md 中的一致式。这里仅使用标准单端素数剩余类分布。

## 7. 双端联合计数接口

定义
\[
C_h(X;a,M)
=
\#\{3<p\le X:\ p,p+h\ {\rm prime},\ p\equiv a\pmod M\}.
\]
把两小波公式逐项限制在双端素数集合上，立即得到
\[
E_h(X)
=
\sum_{\sigma=\pm}
\left[
3C_h(X;\alpha_\sigma,3^L)
-
C_h(X;\alpha_\sigma,3^{L-1})
\right].
\]

父类项又等于三个细子类计数之和，所以每个括号是
\[
2C_{\rm selected}-C_{\rm child,2}-C_{\rm child,3}.
\]

因此研究双端误差的真正对象是联合计数在三个子类之间的偏差，而不是单端
\[
\pi(X;M,a).
\]

若把三个细类计数向量减去其均值，记为层差
\[
D_LC_h,
\]
则权向量是
\[
(2,-1,-1)
\]
且平方范数为 \(6\)。两个根分支总平方范数为 \(12\)。Cauchy 给
\[
|E_h(X)|
\le
\sqrt{12}\|D_LC_h\|_2.
\]
这里只得到接口，不得到新的素数能量上界。

## 8. 一般奇素数有限驻相

令
\[
Q=\ell^{2r},\qquad m=\ell^r,
\]
\[
W_{\ell,r}(z)
=
\ell\mathbf1_{Q\mid z}
-
\mathbf1_{Q/\ell\mid z}.
\]
固定 \(a\bmod m\)，写
\[
n=a+mb.
\]
Taylor 模 \(m^2=Q\)：
\[
P(a+mb)
\equiv
P(a)+mP'(a)b\pmod Q.
\]

若
\[
m\mid P'(a),
\]
则整个块保留，贡献
\[
mW_{\ell,r}(P(a)).
\]

若
\[
v_\ell(P'(a))=t<r,
\]
完全同第 1 节的线性计数：
- 若对应线性同余不可解，两指标都为零；
- 若可解，\(Q\) 层解数为 \(\ell^t\)，\(Q/\ell\) 层解数为 \(\ell^{t+1}\)。

加权差
\[
\ell\cdot\ell^t-\ell^{t+1}=0.
\]

对所有 \(a\bmod m\) 求和，得到
\[
\sum_{n\bmod Q}W_{\ell,r}(P(n))
=
m
\sum_{\substack{a\bmod m\\P'(a)\equiv0\pmod m}}
W_{\ell,r}(P(a)).
\]

## 9. 范围声明

上述第 1–5、7–8 节是有限同余/赋值证明；第 6 节的素数结论使用标准等差数列素数定理及其 Siegel–Walfisz 一致版本。

没有任何一步证明双端素数计数的正下界。尤其不能从单端主项抵消推出
\[
E_h=o(X/\log^2X).
\]

# F₃：树上位移、乘法坐标与仿射相关核

日期：2026-09-28

## 范围与状态

这是一份纸面推导与有限验算记录，不是新颖性声明，也不是 Lean 内核验证报告。
本轮读取了 UyNewNas/omega-balance-prime-lean 中的 F3DeeperExamples.lean、
F3Coordinates.lean 和 F3Rational.lean；没有修改仓库或重跑其 CI。
矩阵／树连接和下述仿射核在这里给出证明，不能据此声称已在 Lean 中完成。

在非奇异点定义
\[
F(x)=v_3(x+1)-v_3(x-1),\qquad x\in\mathbb Q_3\setminus\{-1,1\}.
\]
几何讨论使用通常的赋值，绝不将有限的 totalized `v3 0=0` 用于奇异中心。
在积分和整数平均中，把 F(±1) 任意赋为有限值（本文取 0）；零测集／有限项不影响结论。
记 |0|₃=0，非零 t 的 |t|₃=3^{-v₃(t)}。

## 1. 深度投影不能独立承载普通乘法

F(5)=F(11)=1，F(7)=-1，但
\[
F(5\cdot7)=F(35)=2,\qquad F(11\cdot7)=F(77)=1.
\]
因此即便两个输入都是大于 3 的素数，也不存在函数 H，使
F(mn)=H(F(m),F(n)) 恒成立。

仓库已有 `f3_no_scalar_mul_rule`，正是用这两组素数输入证明该结论。
所以“正负号＋深度”不是完整坐标；要决定同层抵消必须保留更多剩余信息。

## 2. 矩阵的有向树位移

设
\[
M_x=\begin{pmatrix}x&1\\1&x\end{pmatrix},\quad
P=\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
\]
对 x≠±1，M_x 可逆，并且
\[
P^{-1}M_xP=\operatorname{diag}(x+1,x-1).
\]

取 e₊=(1,1)，e₋=(1,-1)，定义格点
\[
\Lambda_j=\mathbb Z_3\,3^j e_+\oplus\mathbb Z_3\,e_-,
\qquad V_j=[\Lambda_j],\quad j\in\mathbb Z.
\]
方括号表示格点的位似类。Bruhat–Tits 树中
\[
d(V_i,V_j)=|i-j|,
\]
因此 {V_j} 构成一条双向无限测地线。

写 x+1=3^r u、x-1=3^s w，其中 u,w 为单位。则
\[
M_x\Lambda_j
=\mathbb Z_3\,3^{j+r}u e_+
 \oplus\mathbb Z_3\,3^s w e_-.
\]
单位不改变生成的 Z₃ 模，整体乘以 3^{-s} 不改变位似类，故
\[
\boxed{M_xV_j=V_{j+r-s}=V_{j+F(x)}.}
\]

这精确规定了轴的方向：j 增大的方向为正。
M_x 的最小位移长度为 |F(x)|。若 F(x)≠0，它是以这条轴为平移轴的双曲等距变换；
若 F(x)=0，它逐点固定这条轴（不必逐点固定整棵树）。
非零位移时，任意顶点向轴的投影与树作用相容，投影的位移就是 |F(x)|，
故任何顶点的位移不小于 |F(x)|，而轴上的顶点达到等号。

这使用的是标准 Bruhat–Tits 树。对 Q₃，它每个顶点有 4 个邻点；
这与 Z₃ 的有根三叉剩余类树不是同一张图，不能混淆。

## 3. 矩阵复合与星运算，不是普通乘法

定义
\[
x\star y=\frac{xy+1}{x+y},\qquad
T(x)=\frac{x+1}{x-1}.
\]
若 x,y≠±1、x+y≠0，则 x⋆y≠±1，且
\[
M_xM_y=(x+y)M_{x\star y},\qquad
T(x\star y)=T(x)T(y).
\]
标量矩阵对格点位似类作用平凡，所以同一轴上的有向位移相加：
\[
\boxed{F(x\star y)=F(x)+F(y).}
\]
同样由 F(x)=v₃(T(x)) 直接得证。

一般而言 M_{xy}≠M_xM_y；绝不能据此声称 F(xy)=F(x)+F(y)。
在 x,y>1 的有理数域上，星运算闭合，但不保持整数性或素数性。
仓库已有有理数 Cayley 坐标、星运算与可加性的证明项。

## 4. 普通乘法的完整坐标

对 x∈Z₃× 定义 ε(x)∈{1,-1}，使 ε(x)≡x mod 3，并设
\[
U(x)=\varepsilon(x)x\in1+3\mathbb Z_3,\qquad
z(x)=U(x)-1\in3\mathbb Z_3.
\]
每个 x 唯一写成 ε(1+z)，所以 (ε,z) 是完整坐标。
在 x≠±1 时，
\[
F(x)=-\varepsilon(x)v_3(z(x)).
\]

普通乘法的坐标法则是
\[
(\varepsilon,z)\cdot(\eta,w)
=(\varepsilon\eta,z+w+zw).
\]
因此“异层取小、同层可能升层”正是乘法形式群 z+w+zw 的赋值行为。
若 z=3^k A、w=3^k B，则
\[
|F(xy)|=k+v_3(A+B+3^kAB),
\]
前提 xy≠±1；对正整数 x,y>1 自动满足。
若两输入恰好同层 k≥1，则 A,B 是单位，首次升层等价于 3 | A+B。
这已经在仓库的整数坐标中提供了相应证明项。

标准 3-进对数在 1+3Z₃ 上是到 3Z₃ 的等距群同构。
令
\[
L(x)=\log_{3\text{-adic}}U(x).
\]
则
\[
L(xy)=L(x)+L(y),\qquad v_3(L(x))=v_3(z(x)).
\]
所以
\[
\boxed{F(x)=-\varepsilon(x)v_3(L(x)).}
\]
这里的对数不是实数的“以 3 为底的对数”。

例如对 n>1、3∤n、e≥1：
\[
F(n^e)=-\varepsilon(n)^e\bigl(|F(n)|+v_3(e)\bigr).
\]

## 5. 本轮整理的仿射相关公式

令 μ 为 Z₃ 上总质量为 1 的加法 Haar 测度。
对 a∈Z₃×、b∈Z₃，定义
\[
C(a,b)=\int_{\mathbb Z_3}F(x)F(ax+b)\,d\mu(x).
\]
则
\[
\boxed{
C(a,b)=
|b-(a+1)|_3+|b+(a+1)|_3
-|b-(a-1)|_3-|b+(a-1)|_3.}
\]

### 5.1 基础双中心积分

令
\[
B(t)=\int_{\mathbb Z_3}v_3(x)v_3(x+t)\,d\mu(x).
\]
赋值在 0 的取值不影响积分。利用
\[
v_3(x)=\sum_{j\ge1}\mathbf1_{3^j\mid x}
\quad\text{（几乎处处）}
\]
以及两剩余类的交集测度，
\[
\mu(3^j\mid x,\ 3^k\mid x+t)
=
\begin{cases}
3^{-\max(j,k)},&3^{\min(j,k)}\mid t,\\
0,&\text{否则},
\end{cases}
\]
由非负项的 Tonelli 定理得到
\[
B(0)=\sum_{j,k\ge1}3^{-\max(j,k)}
=\sum_{r\ge1}(2r-1)3^{-r}=1.
\]
若 t≠0、d=v₃(t)，被去掉的恰是 j,k≥d+1 的部分，其和为 3^{-d}B(0)，故
\[
\boxed{B(t)=1-|t|_3}
\]
对 t=0 也成立。

### 5.2 展开四项

因为 a 是单位，
\[
v_3(ax+b\pm1)=v_3\left(x+\frac{b\pm1}{a}\right).
\]
四项展开给出
\[
C(a,b)
=B(b+1-a)-B(b-1-a)-B(b+1+a)+B(b-1+a).
\]
这里省略分母 a 不改变赋值或 3-进范数。代入 B(t)=1-|t|₃，即得所述公式。

### 5.3 平移与纯乘法都是特例

取 a=1：
\[
C(1,h)=|h-2|_3+|h+2|_3-2|h|_3.
\]
取 b=0：
\[
\boxed{C(a,0)=2(|a+1|_3-|a-1|_3).}
\]

对 a∈Z₃×、a≠±1，设 d=|F(a)|，则
\[
\boxed{
C(a,0)=-2\,\operatorname{sgn}F(a)\,(1-3^{-d})
       =2\varepsilon(a)(1-|L(a)|_3).}
\]
在 a=1 和 a=-1 时直接取 C(1,0)=2、C(-1,0)=-2。
因此普通乘法导致的平均相关系数精确恢复 F(a) 的符号和层级：
归一化相关系数 ρ=C/2 的符号为 -sgn F(a)，
且 d=-log₃(1-|ρ|)（这里 log₃ 是实数对数）。

注意：此处平均遍历 Z₃ 或所有整数，不是对素数对取平均。

### 5.4 整数 Cesàro 版本

若 a,b 为固定整数且 3∤a，则令 F(±1)=0 后也有
\[
\lim_{N\to\infty}\frac1N\sum_{n=2}^{N}F(n)F(an+b)=C(a,b).
\]
负整数输入按同样的有符号整数赋值定义。

证明极限交换的细节如下。设
\[
v_R(y)=\sum_{j=1}^{R}\mathbf1_{3^j\mid y},\qquad
F_R(y)=v_R(y+1)-v_R(y-1).
\]
固定 R 后，F_R(n)F_R(an+b) 是模 3^R 的周期函数，其整数平均等于完整周期平均。

对固定整数 c 且 3∤a，非零线性值 an+c 的赋值不超过 O_{a,c}(log N)。
又有每个 k 的整除计数 N/3^k+O(1)。
由恒等式 t²=Σ_{j=1}^t(2j-1)，对零点单独去掉，得到
\[
\limsup_{N\to\infty}
\frac1N\sum_{n=2}^N
\bigl(v_3(an+c)-v_R(an+c)\bigr)^2
\le
\sum_{j\ge1}(2j-1)3^{-(R+j)}
=3^{-R}.
\]
O(1) 计数误差总计 O_{a,c}((log N)²/N)，趋于 0。
线性值为 0 至多一次，其固定 R 的贡献同样趋于 0。

从 (u-v)²≤2u²+2v² 得
\[
\limsup_N\frac1N\sum(F(an+b)-F_R(an+b))^2\le4\,3^{-R}.
\]
同样适用于 F(n)。原函数和截断函数的均方平均有界，
故 Cauchy–Schwarz 保证相关平均的截断误差随 R→∞ 消失。
再用 Haar 空间中相同的 L² 收敛，即把周期平均的极限识别为上面的积分 C(a,b)。

## 6. 仿射作用也能送进同一个 Cayley 坐标

T 是射影直线上的对合。若 t=T(x)，则
\[
T(ax+b)=
\frac{(a+b+1)t+(a-b-1)}
     {(a+b-1)t+(a-b+1)}.
\]
对应矩阵的行列式为 4a。对 a∈Z₃×、b∈Z₃，这是 GL₂(Z₃) 中的矩阵。
Cayley 坐标把原来的两个中心 +1、-1 送到 ∞、0。
这些共轭后的仿射变换也给出树作用，但一般不保持 t 坐标中由 0、∞ 决定的轴。
因此仅保留 v₃(t)=F(x) 不能决定变换后的层级；必须保留 t 的更多信息。

## 7. 与一般素数 ℓ 的关系

矩阵的特征值法和轴位移构造对任意素数 ℓ 都成立。
一般基础核是
\[
B_\ell(t)=\frac{\ell+1}{(\ell-1)^2}(1-|t|_\ell).
\]
所以同一仿射相关公式也成立，只需把 3-进范数换成 ℓ-进范数，
并乘以 (\ell+1)/(\ell-1)²；条件改为 ℓ∤a。
在 ℓ=3 时这个系数恰为 1。

因此树和相关结构本身不是 3 专有的新结构。
3 的特殊性在于：单位剩余类只有 ±1，故所有大于 3 的素数都进入非零层，
并且间距 2 的素数对被模 3 条件强制安排在相反等层。
这些事实本身不提供素数对存在性的估计。

## 8. 验算记录与新颖性边界

`verify_f3_geometry.py` 不依赖第三方包。
它对 R=1,...,9、-10≤a,b≤10、3∤a 的全部 2646 组参数，
逐项遍历完整的 3^R 周期，并用精确分数比较有限重叠公式。
全部相等。R=9 的周期相关与无限公式的最大差为 20/19683。
这验证有限公式及代码，不代替上面的无限范围证明。

另用 SymPy 符号验证了：矩阵对角化、矩阵星运算关系、
Cayley 星运算关系、Cayley 对合、仿射共轭式，共 5 个恒等式。

树、主单位群对数、Cayley 共轭和剩余类计数都是经典材料。
本文对 F₃ 的统一整理以及仿射公式不能仅凭本轮检索就宣称首次发现。
作为论文结构，适合暂称“F₃ 的两中心几何与仿射相关”，
但是否形成有独立研究贡献的主定理仍须文献对照和进一步应用。
本记录不声称证明孪生素数无穷性。

## 来源

- Judith Ludwig and Christian Merten, *Formalising the Bruhat–Tits Tree*,
  Annals of Formalized Mathematics 2 (2026), 55–81.
  第 3 节：格点、距离、树作用；论文也说明了已有的 Lean 基础。
  https://arxiv.org/html/2505.12933v4
- Keith Conrad, *Infinite Series in p-adic Fields*,
  Theorem 8.5、Theorem 8.7、Example 8.9、Theorem 8.13：
  p-进对数同态、等距性及指数对数互逆。
  https://kconrad.math.uconn.edu/blurbs/gradnumthy/infseriespadic.pdf
- 用户仓库已读取源码：
  https://github.com/UyNewNas/omega-balance-prime-lean/blob/master/OmegaBalance/F3DeeperExamples.lean
  https://github.com/UyNewNas/omega-balance-prime-lean/blob/master/OmegaBalance/F3Coordinates.lean
  https://github.com/UyNewNas/omega-balance-prime-lean/blob/master/OmegaBalance/F3Rational.lean
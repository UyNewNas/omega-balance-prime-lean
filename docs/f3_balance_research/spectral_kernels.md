# 乘积核的谱与短带匹配

设 $r\ge1$，$Q=3^{2r}$、$q=Q/3$，
\[
W_r(z)=3\mathbf1_{Q\mid z}-\mathbf1_{q\mid z},\qquad e_N(x)=\exp(2\pi ix/N).
\]
内积采用未归一化的计数内积。

## 1. Ramanujan 和及特征展开

### 命题 1.1

令 $c_Q(z)=\sum_{u\bmod Q,(u,Q)=1}e_Q(uz)$。则
\[
W_r(z)=c_Q(z)/q.
\]
若 $3\nmid ab$，还有
\[
W_r(ab+1)=\frac3{\varphi(Q)}
\sum_{\substack{\chi\bmod Q\\\operatorname{cond}(\chi)=Q}}
\chi(-1)\chi(a)\chi(b).
\]

**证明。** 全部模 $Q$ 加性特征之和为 $Q\mathbf1_{Q\mid z}$；减去频率被 $3$ 整除的部分，得到 $c_Q(z)=Q\mathbf1_{Q\mid z}-q\mathbf1_{q\mid z}$。乘法特征公式由模 $Q$ 与模 $q$ 的正交关系相减得到：$\varphi(Q)=3\varphi(q)$，从模 $q$ 提升的特征恰好相消。$\square$

### 命题 1.2（根计数的 Fourier 变换）

令 $R_R(h)=\#\{n\bmod3^R:n(n+h)+1\equiv0\pmod{3^R}\}$。则
\[
\sum_{h\bmod3^R}R_R(h)e_{3^R}(ah)
=\sum_{u\bmod3^R}^{*}e_{3^R}(-a(u+u^{-1})).
\]
特别地，当 $R=2r$、$3\nmid a$ 时，右边等于
\[
3^r\bigl(e_Q(-2a)+e_Q(2a)\bigr).
\]

**证明。** 每个单位 $u$ 唯一确定 $h=-u-u^{-1}$，先交换两个有限求和即得第一式。第二式将 $u=x+3^ry$ 分块：模 $Q$ 下相位的线性项为 $-a3^ry(1-x^{-2})$。对 $y$ 求和后，只有 $x^2\equiv1\pmod{3^r}$ 保留。两个单位根为 $x=\pm1$，对应常相位 $\mp2a$，每块贡献 $3^r$ 倍。$\square$

## 2. 完整乘积核

令 $G=(\mathbb Z/Q\mathbb Z)^\times$，并定义
\[
(\mathcal Kf)(a)=\sum_{b\in G}W_r(ab+1)f(b).
\]
令
\[
(Pf)(a)=\frac13\sum_{b\equiv a\ (q)}f(b),\quad D=I-P,
\quad \tau(a)=-a^{-1},\quad(Rf)(a)=f(\tau(a)).
\]

### 定理 2.1

$P,D$ 为正交投影，$R$ 为自伴对合，且
\[
\mathcal K=3RD=3DR,\qquad\mathcal K^2=9D.
\]
$\mathcal K$ 的特征值为 $-3,0,3$，各自重数均为 $|G|/3$。

**证明。** 对固定 $a$，模 $Q$ 的唯一正权位置为 $\tau(a)$，模 $q$ 的同一父类其余两个位置权为 $-1$。因此
\[
(\mathcal Kf)(a)=3f(\tau(a))-
\sum_{b\equiv\tau(a)\ (q)}f(b)=3(RDf)(a).
\]
$\tau$ 将父类双射到父类，故 $R$ 与 $P,D$ 交换。平方后用 $R^2=I,D^2=D$ 得 $\mathcal K^2=9D$。$D$ 的秩为 $2|G|/3$，故非零特征值绝对值为 $3$。又 $a^2+1$ 不被 $3$ 整除，所以核的对角线全零，迹为零，正负重数相等。$\square$

### 推论 2.2（能量恒等式）

对实向量 $f$，令 $g=Df$、$g_\pm=(g\pm Rg)/2$。则
\[
\langle f,\mathcal Kf\rangle
=3(\|g_+\|_2^2-\|g_-\|_2^2).
\]
对复向量 $f,g$，有尖锐界
\[
|\langle f,\mathcal Kg\rangle|\le3\|Df\|_2\|Dg\|_2.
\]

**证明。** $R$ 的正负特征子空间正交；在 $D$ 的像上使用 $\mathcal K=3R$。双线性界由 Cauchy–Schwarz 得到，取特征向量可达等号。$\square$

核不普遍半正定，即使向量非负且支撑于素数：$r=3$ 时，仅在 $5,97$ 处放权 $1$，由于 $5\cdot97+1=2\cdot3^5$，二次型为 $-2$。

### 命题 2.3（不同层的线性组合）

固定 $R_0$，将 $1\le r\le R_0$ 的完整核提升到模 $3^{2R_0}$ 的单位空间。任何非零的实系数线性组合 $\sum_r c_r\mathcal K_r$ 都有正、负特征值。

**证明。** 令 $E_j$ 为模 $3^j$ 的条件均值，$D_j=E_j-E_{j-1}$。提升后的算子为
\[
\mathcal K_r=3\cdot3^{2R_0-2r}R D_{2r}.
\]
不同 $D_{2r}$ 正交。每层取同一个父类内两个子类的指示差 $e$；$e$ 与 $Re$ 分别支撑在不同模 $3$ 侧，因此 $e+Re,e-Re$ 均非零，分别为该层上的正负特征向量。选任一 $c_r\ne0$ 即得。$\square$

### 命题 2.4（短区间投影范数）

若整数区间 $I$ 的直径小于 $q$，将系数 $c_n$（$n\in I$、$3\nmid n$）嵌入模 $Q$ 的向量 $f$，则
\[
\|Df\|_2^2=\frac23\sum_{n\in I,3\nmid n}|c_n|^2.
\]

**证明。** 每个父类最多占据一个整数。单个非零坐标的投影是 $c(2/3,-1/3,-1/3)$，平方范数为 $2|c|^2/3$；不同父类正交。$\square$

## 3. 整数短带核

在任意有限整数顶点集上，定义
\[
B_{r,H}(a,b)=\mathbf1_{0<|a-b|\le H}
\mathbf1_{a\equiv b\ (2)}W_r(ab+1).
\]

### 定理 3.1（匹配分解）

若 $H<q$，每个顶点至多有一个非零权伙伴。因此矩阵是零块与
\[
\begin{pmatrix}0&w\\w&0\end{pmatrix},\qquad w\in\{2,-1\}
\]
的直和，非零特征值只能为 $\pm2,\pm1$。

**证明。** 若 $b,c$ 都是 $a$ 的伙伴，则 $ab\equiv ac\equiv-1\pmod q$。$a$ 可逆，故 $q\mid b-c$；又 $b,c$ 同奇偶，所以 $2q\mid b-c$。但 $|b-c|\le2H<2q$，只能有 $b=c$。每个二点块的特征值为 $\pm|w|$。$\square$

### 定理 3.2（首次分叉带宽）

设 $r\ge2$。全体整数上的同奇偶图在 $H\le q+10$ 时仍为匹配；在 $H=q+11$ 时存在度至少为 $2$ 的顶点，且可使相关顶点均为正奇数。

**证明。** 只需考虑 $q\le H\le q+10<2q$。两个不同伙伴相差 $2q$，可写为
\[
b=a+d-q,\qquad c=a+d+q,
\]
其中 $d$ 为奇数且 $|d|\le H-q\le10$。非零权要求 $a^2+da+1\equiv0\pmod q$。当 $|d|=1,3,5,7,9$ 时，判别式分别为 $-3,5,21,45,77$，均不是模 $27$ 的平方；而 $27\mid q$，故无根。

当 $d=11$ 时，判别式为 $117=9\cdot13$。$13$ 模 $3$ 为平方单位，其两个简单根可以逐层提升，所以方程在每个 $q$ 上有根。选择充分大且奇的代表 $a$，上述两个伙伴给出长度 $q-11$ 和 $q+11$ 的非零边。$\square$

## 4. 互素局部筛的精确分解

设 $d$ 为与 $3$ 互素的平方自由整数，令 $\nu_\ell(h)=1$（$\ell\mid h$）或 $2$（$\ell\nmid h$）。则
\[
\#\{n\bmod3^R d:3^R\mid n(n+h)+1,\ (n(n+h),d)=1\}
=R_R(h)\prod_{\ell\mid d}(\ell-\nu_\ell(h)).
\]

**证明。** 模 $3^R$ 的条件有 $R_R(h)$ 个解；对每个 $\ell\mid d$，被排除的类为 $0,-h$，重合当且仅当 $\ell\mid h$。中国剩余定理相乘。$\square$

## 参考

Ramanujan 和及相关有限矩阵的背景可见 N. Ushiroya, *Eigenvalues of Matrices whose Elements are Ramanujan Sums or Kloosterman Sums*：https://arxiv.org/abs/1803.02970 。本文的乘积核恒等式和短带结论均由上述证明给出。

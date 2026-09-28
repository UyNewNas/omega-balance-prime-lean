# 平衡逆元对的层级几何

对 $n>1$，定义 $F_3(n)=v_3(n+1)-v_3(n-1)$。本文件计数有序奇数对；不要求端点为素数。设 $m=3^r$，研究
\[
1<a,b<m,\qquad ab\equiv1\pmod m.
\]

## 1. 平方根深度边界

### 定理 1.1

上述数对满足
\[
F_3(a)=F_3(b),\qquad2|F_3(a)|<r.
\]

**证明。** 取 $\epsilon\in\{\pm1\}$ 满足 $a\equiv\epsilon\pmod3$。奇数 $1<a<m$ 不可能同余于 $\pm1\pmod m$，故 $j=v_3(a-\epsilon)$ 满足 $1\le j<r$。由
\[
a(b-\epsilon)\equiv-\epsilon(a-\epsilon)\pmod m
\]
得到 $v_3(b-\epsilon)=j$，所以两端的 $F_3$ 都为 $-\epsilon j$。

若 $2j\ge r$，则 $m\mid(a-\epsilon)(b-\epsilon)$。这个乘积是偶数，故亦被 $2m$ 整除；$ab-1$ 同样被 $2m$ 整除。展开相减给出
\[
a+b\equiv2\epsilon\pmod{2m}.
\]
但 $6\le a+b\le2m-4$，这个区间没有模 $2m$ 同余于 $2$ 或 $-2$ 的数，矛盾。$\square$

两个因子均小于 $m$ 的假设不可省略。例如 $m=81$、$(a,b)=(17,143)$ 时，$ab\equiv1\pmod m$ 且两端 $F_3$ 均为 $2$，但 $2\cdot2=r$。

## 2. 全部可行层的二次正规形

写
\[
r=2j+c,\quad j,c\ge1,\quad t=3^j,\quad s=3^c,\quad m=t^2s.
\]
固定 $\epsilon=\pm1$，对应有符号层 $F_3=-\epsilon j$。

### 定理 2.1

满足 $F_3(a)=F_3(b)=-\epsilon j$ 的平衡逆元对，与以下参数一一对应：
\[
a=\epsilon+2tu,\quad b=\epsilon+2tv,\quad
1\le u,v\le(ts-1)/2,
\]
\[
u+v=th,\quad1\le h<s,\quad3\nmid u,
\quad2u^2-2thu-\epsilon h\equiv0\pmod s.
\]
可行的 $h$ 恰满足 $h\equiv-\epsilon\pmod3$；对每个这样的 $h$，模 $s$ 恰有两个单位根。

**证明。** 同层及奇偶条件给出 $a=\epsilon+2tu,b=\epsilon+2tv$，边界给出统一上限 $(ts-1)/2$。由于 $ab-1$ 为偶数，乘积条件等价于
\[
\epsilon(u+v)+2tuv\equiv0\pmod{ts}.
\]
先模 $t$ 得 $u+v=th$，再除以 $t$ 并代入 $v=th-u$，得到二次方程。模 $3$ 下，它变成 $2u^2\equiv\epsilon h$；单位解存在当且仅当 $h\equiv-\epsilon$，此时两根为 $1,2$。导数 $4u-2th$ 为单位，每根逐次唯一提升。反向代入证明充分性，并有 $v\equiv-u\pmod3$。$\square$

等价的完成平方形式为
\[
(2u-th)^2\equiv t^2h^2+2\epsilon h\pmod s.
\]
每个模 $s$ 根 $u_0$ 给出一个算术数列分支：
\[
a=\epsilon+2tu_0+2ts\ell,\qquad
b=\epsilon+2t(th-u_0)-2ts\ell,\qquad\ell\in\mathbb Z,
\]
并按端点条件截取 $\ell$ 的连续整数区间。

若额外满足 $c\le j$，则 $s\mid t$，根方程简化为 $2u^2\equiv\epsilon h\pmod s$。不满足该条件时必须保留 $-2thu$ 项。

## 3. 盒计数与斜线极限

取固定矩形 $R=(\alpha,\beta]\times(\gamma,\delta]\subset[0,1]^2$，面积为 $\mathcal A>0$。定义
\[
\ell_R(z)=[\min(\beta,z-\gamma)-\max(\alpha,z-\delta)]_+.
\]
它是连续分段线性函数，总变差有绝对上界，且 $\int\ell_R(z)\,dz=\mathcal A$。

### 定理 3.1

记 $N_{j,c,\epsilon}(R)$ 为第 2 节的层在归一化盒子 $(a/m,b/m)\in R$ 中的点数。则
\[
N_{j,c,\epsilon}(R)
=t\sum_{\substack{1\le h<s\\h\equiv-\epsilon\ (3)}}\ell_R(2h/s)+O(s).
\]
因此
\[
N_{j,c,\epsilon}(R)=\frac{ts}{6}\mathcal A+O(t+s).
\]

**证明。** 每条线满足
\[
a+b=2\epsilon+2t^2h,\qquad
(a+b)/m=2h/s+2\epsilon/m.
\]
每个根分支在归一化 $a$ 坐标上的步长为 $2/t$，故一个分支在线段上的计数为 $(t/2)\ell_R(2h/s+2\epsilon/m)+O(1)$。两个分支相加，再对 $s/3$ 条线求和。平移带来的总改变为 $O(ts/m)$，被 $O(s)$ 吸收。第二式由步长 $6/s$ 的 Riemann 和及 $\ell_R$ 的有界变差得到。$\square$

固定 $c$ 并令 $j\to\infty$，对连续函数 $f$，有
\[
\frac1t\sum f(a/m,b/m)
\longrightarrow
\sum_{\substack{1\le h<s\\h\equiv-\epsilon\ (3)}}
\int_{\max(0,2h/s-1)}^{\min(1,2h/s)}f(x,2h/s-x)\,dx.
\]
这是有限条线上的非归一化极限测度。证明是在每个分支上使用一维 Riemann 和。若 $t,s$ 同时趋于无穷，则定理 3.1 给出面积主项的相对误差 $O_R(t^{-1}+s^{-1})$。

## 4. 临界带的精确计数

### 定理 4.1（完整正方形）

在 $1\le c\le j$ 时，每个符号层的有序对数恰为
\[
\frac{ts}{6}+\frac{t}{2s}
=\frac{3^{r-j}}6+\frac{3^{3j-r}}2.
\]

**证明。** 固定可行 $h$。当 $h<s/2$，$u$ 的区间是 $[1,th-1]$；由于 $s\mid t$，每个单位根出现 $th/s$ 次，共 $2th/s$ 点。当 $h>s/2$，区间为 $[th-U,U]$，$U=(ts-1)/2$，两个根共出现 $2t(s-h)/s$ 次。总数为
\[
\frac{2t}{s}\sum_{\substack{1\le h<s\\h\equiv-\epsilon\ (3)}}\min(h,s-h).
\]
将等差数列在 $s/2$ 处分段求和，得 $(s^2+3)/12$。两个符号由 $h\mapsto s-h$ 对应。代入即得。$\square$

### 定理 4.2（单侧盒）

令 $c=2$、$j\ge2$，取
\[
R=(1/4,1/3]\times(1/2,2/3].
\]
用 $N_{\pm j}$ 表示 $F_3$ 的符号，则
\[
N_{+j}(R)=\begin{cases}(3^j+3)/12,&j\text{ 偶},\\(3^j+9)/12,&j\text{ 奇},\end{cases}
\qquad N_{-j}(R)=0.
\]

**证明。** $s=9$。正层 $\epsilon=-1$ 的可行 $h$ 为 $1,4,7$，负层为 $2,5,8$。盒中的坐标和位于 $(3/4,1]$，故仅正层 $h=4$ 的线穿过盒子。该线在 $a$ 方向覆盖整个 $(m/4,m/3]$，其单位根为 $u\equiv4,5\pmod9$。

置 $t=3^j$。须计数
\[
L<u\le U,\quad u\equiv4,5\pmod9,
\quad L=\lfloor9t/8\rfloor,\quad U=(3t-1)/2.
\]
计数等于
\[
\sum_{e=4,5}\left(\left\lfloor\frac{U-e}{9}\right\rfloor-
\left\lfloor\frac{L-e}{9}\right\rfloor\right).
\]
对 $j\ge2$，$3^j\bmod72$ 在 $j$ 偶时为 $9$、奇时为 $27$。分别代入上述整数部分式，得到所列两个值。$\square$

### 推论 4.3（统一平方根误差的下限）

在定理 4.2 的固定盒子中，另取偶数 $r$ 及深度阈值 $t=3^{r/2}$。满足 $a\equiv\pm1\pmod t$ 的奇逆元对计数为零，而面积型整数主项为
\[
\frac{AB}{2mt}=\frac{\sqrt m}{144}+o(\sqrt m),
\]
其中 $A,B$ 为两个实际整数区间的长度。因此，允许深度变化时，该面积主项的统一误差不能为 $o(\sqrt m)$。

**证明。** 定理 1.1 排除全部这些深度。区间长度满足 $AB=m^2/72+O(m)$，直接代入。$\square$

## 5. 斜线上的局部根数

### 命题 5.1

对素数 $\ell\ge5$ 及整数 $C$，有
\[
\rho_\ell(C):=\#\{a\bmod\ell:\ell\mid a(C-a)(a(C-a)-2)\}
=3-\mathbf1_{\ell\mid C}+\left(\frac{C^2-8}{\ell}\right).
\]

**证明。** $a=0$ 或 $a=C$ 贡献 $2-\mathbf1_{\ell\mid C}$ 个点。方程 $a(C-a)=2$ 的判别式为 $C^2-8$，贡献 $1+((C^2-8)/\ell)$ 个点，且与前两类不交。$\square$

特别地 $0\le\rho_\ell(C)\le4<\ell$。对平方自由 $d$、$(d,6)=1$，定义 $\rho_h(d)=\prod_{\ell\mid d}\rho_\ell(C_h)$，$C_h=2\epsilon+2t^2h$。当 $h$ 按公差 $3$ 遍历一个模 $d$ 周期时，
\[
\frac1d\sum_h\frac{\rho_h(d)}d
=\prod_{\ell\mid d}\frac{3\ell-2}{\ell^2}.
\]
因为 $C_h$ 的公差 $6t^2$ 与 $d$ 互素；模 $\ell$ 下全部坏点 $(a,b)$ 共 $3\ell-2$ 个，随后使用中国剩余定理。

## 参考

- A. Bower, R. Evans, V. Luo, S. J. Miller, *Coordinate sum and difference sets of d-dimensional modular hyperbolas*：https://arxiv.org/abs/1212.2930 。
- I. E. Shparlinski, *Modular Hyperbolas*：https://arxiv.org/abs/1103.2879 。

所用简单根提升、模逆元及坐标和方法属于经典理论；本文件的计数结论由上述推导给出。

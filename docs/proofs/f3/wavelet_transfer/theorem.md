# F3-WAV：三进层提升、小波分解与一致筛权传递

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-WAV-1\` 至 \`F3-WAV-6\` |
| 来源 | “F3探索2”最新一轮：research_notes_round2.md（2026-09-28） |
| 状态 | \`PAPER-AUDITED\` |
| Lean 状态 | 尚未形式化 |
| 外部依赖 | 等差数列素数定理 / Siegel–Walfisz；其余主局部结论为初等有限同余与 Hensel 型提升 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 定义

令
\[
Q=3^{2r},\qquad m=3^r,
\]
\[
W_r(z)=3\mathbf1_{Q\mid z}-\mathbf1_{Q/3\mid z},
\qquad
w_{r,h}(n)=W_r(n(n+h)+1),
\]
并记
\[
D_h=h^2-4.
\]

\(W_r\) 是 Ramanujan 和 \(c_Q\) 的归一化：
\[
W_r(z)=\frac{c_Q(z)}{3^{2r-1}}.
\]

## 2. F3-WAV-1：条件传递

令 \(a_c\pmod m\) 为
\[
2a_c+h\equiv0\pmod m
\]
的唯一类。则对每个 \(a\pmod m\),
\[
\boxed{
\sum_{b=0}^{m-1}w_{r,h}(a+mb)
=
mW_r(D_h)\mathbf1_{a=a_c}.
}
\]
因此任意 \(B:\mathbb Z/m\mathbb Z\to\mathbb C\) 满足
\[
\boxed{
\sum_{n\bmod Q}B(n\bmod m)w_{r,h}(n)
=
mB(a_c)W_r(D_h).
}
\]

在
\[
r\ge2,\qquad 2\le H<3^{2r-1}-2
\]
且 \(2\le h\le H\) 时：

- \(h>2\) 的每个低位块和为 \(0\)；
- \(h=2\) 有
  \[
  \boxed{w_{r,2}(n)=2\mathbf1_{n\equiv-1\pmod m}.}
  \]

## 3. F3-WAV-2：两小波精确分解

设 \(h>2\)，\(t=v_3(D_h)<2r-1\)。

若 \(t\) 为奇数，或 \(t=2s\) 但
\[
D_h/3^{2s}\equiv2\pmod3,
\]
则 \(w_{r,h}\equiv0\)。

其余情形写
\[
t=2s,\qquad D_h/3^{2s}\equiv1\pmod3,
\qquad L=2r-s,\qquad M=3^L.
\]
存在两个互不相交的三进根类 \(\alpha_\pm\bmod M\)，使
\[
\boxed{
w_{r,h}(n)
=
\psi_{L,\alpha_+}(n)+\psi_{L,\alpha_-}(n),
}
\]
其中
\[
\psi_{L,a}(n)
=
3\mathbf1_{n\equiv a\pmod{3^L}}
-
\mathbf1_{n\equiv a\pmod{3^{L-1}}}.
\]

每个父类的三个子类权值为 \((2,-1,-1)\)。

其 Fourier 支撑只在 \(3\nmid\xi\)：
\[
\widehat\psi(\xi)=
\begin{cases}
\dfrac3M e_M(-\xi a),&3\nmid\xi,\\
0,&3\mid\xi.
\end{cases}
\]
并且
\[
\boxed{\sum_{n\bmod M}w_{r,h}(n)^2=12.}
\]

## 4. F3-WAV-3：任意有限单位公差 AP 上的常数界

在上述短位移范围，\(h>2\)，若 \(3\nmid d\)，则任意整数 \(a\) 和任意连续有限指标区间 \(J\) 都有
\[
\boxed{
\left|
\sum_{j\in J}w_{r,h}(a+dj)
\right|\le4.
}
\]

## 5. F3-WAV-4：有限除数和传递

设有限支撑 \(a_d,b_e\) 只支撑在 \(3\nmid de\)，定义
\[
A(n)=\sum_{d\mid n}a_d,
\qquad
B(n)=\sum_{e\mid n}b_e,
\]
\[
U=\sum_d|a_d|,
\qquad
V=\sum_e|b_e|.
\]
则
\[
\boxed{
\sum_{n\le X}A(n)B(n+h)w_{r,h}(n)
=
\mathbf1_{h=2}\frac{2X}{3^r}
\sum_{(d,e)\mid2}
\frac{a_db_e}{\operatorname{lcm}(d,e)}
+\mathcal E_h,
}
\]
其中更精确地求和条件是 \(\gcd(d,e)\mid2\)，且
\[
\boxed{|\mathcal E_h|\le4UV;}
\]
当 \(h=2\) 时常数可改为 \(2\)。

## 6. F3-WAV-5：一个端点为素数的无条件渐近

固定 \(r,H\) 满足窗口。则
\[
\boxed{
\frac1{\pi(X)}
\sum_{3<p\le X}w_{r,h}(p)
\longrightarrow
\begin{cases}
3^{1-r},&h=2,\\
0,&2<h\le H.
\end{cases}
}
\]
这里不要求 \(p+h\) 为素数。

在 \(Q\le(\log X)^B\) 时，Siegel–Walfisz 给出任意固定 \(A,B>0\) 的一致式
\[
\sum_{3<p\le X}w_{r,h}(p)
=
\mathbf1_{h=2}3^{1-r}\operatorname{Li}(X)
+
O_{A,B}\!\left(\frac{X}{(\log X)^A}\right).
\]

## 7. F3-WAV-6：一般有限驻相公式

对任意奇素数 \(\ell\)、\(r\ge1\)、\(P\in\mathbb Z[x]\)，令
\[
Q=\ell^{2r},\quad m=\ell^r,\quad
W_{\ell,r}=\ell\mathbf1_Q-\mathbf1_{Q/\ell}.
\]
则
\[
\boxed{
\sum_{n\bmod Q}W_{\ell,r}(P(n))
=
m
\sum_{\substack{a\bmod m\\P'(a)\equiv0\pmod m}}
W_{\ell,r}(P(a)).
}
\]

## 8. 双端素数边界

对
\[
C_h(X;a,M)
=
\#\{3<p\le X:\ p,p+h\ {\rm prime},\ p\equiv a\pmod M\}
\]
有精确接口
\[
E_h(X)
=
\sum_{\sigma=\pm}
\bigl[
3C_h(X;\alpha_\sigma,3^L)
-
C_h(X;\alpha_\sigma,3^{L-1})
\bigr].
\]

本证明包**没有**证明：
- \(E_h=o(X/\log^2X)\)；
- 双端素数正下界；
- 孪生素数无穷性。

单端素数等分布不能替代双端联合剩余类分布。

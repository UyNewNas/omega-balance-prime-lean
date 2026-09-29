# F3-PEAK：有效双峰间隔、第二极值与单异常点剔除

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-PEAK-1\`、\`F3-PEAK-2\`、\`F3-PEAK-3\`、\`F3-PEAK-4\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源研究稿 | [F3_effective_peak_separation.md](../../../f3_balance_research/F3_effective_peak_separation.md) |
| Lean 状态 | 尚未形式化 |
| 外部依赖 | 核心有效定理为初等整数/三进证明；Hensel 用于任意高孤峰构造；S-部分定理只用于与前轮最高峰结果比较 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 固定整数双根过程

固定
\[
k\ge1,\qquad q=3^k,\qquad n,d>1
\]
并满足
\[
d\equiv1\pmod3,
\qquad
v_3(Q_0),v_3(Q_1)\ge2k+1,
\]
其中
\[
Q_j
=
(n+2jqd)(n+(2jq+2)d)+1.
\]

令
\[
D_j=v_3(Q_j),
\qquad
e_j=D_j-2k.
\]

写
\[
K=(n+d)/q,\qquad
g=\gcd(K,d),\qquad
A=K/g,\quad B=d/g.
\]
则
\[
A,B>0,\qquad (A,B)=1,\qquad3\nmid B,
\]
并且两个三进根满足
\[
r_0+r_1=-A/B.
\]

## 2. 定理 F3-PEAK-1：双峰整除与有效分离

对任意
\[
0\le i<j,
\qquad
t=\min(e_i,e_j),
\]
若 \(t\ge1\)，则
\[
\boxed{
\begin{cases}
3^t\mid j-i,&i\equiv j\pmod3,\\
3^t\mid B(i+j)+A,&i\not\equiv j\pmod3.
\end{cases}
}
\]

若
\[
e_i\ne e_j,
\]
相应被整除整数的三进赋值恰为 \(t\)。

因此统一有
\[
\boxed{
3^{\min(e_i,e_j)}
\le
A+B(i+j).
}
\]

这是全范围、有效、初等的双峰限制。

## 3. 定理 F3-PEAK-2：第二极值的有效 \(\log N+O(1)\) 界

对 \(N\ge3\)，把
\[
D_0,\ldots,D_{N-1}
\]
按大小排列，记最大值和第二大值为
\[
M_1(N),\qquad M_2(N),
\]
重复值按不同索引计。

则
\[
\boxed{
2k+\lfloor\log_3N\rfloor
\le
M_2(N)
\le
2k+
\left\lfloor
\log_3(A+B(2N-3))
\right\rfloor.
}
\]

所以
\[
\boxed{
M_2(N)
=
2k+\log_3N+O_{A,B}(1)
}
\]
且上下界对每个 \(N\) 都显式可计算。

若
\[
H(N)=
\left\lfloor
\log_3(A+B(2N-3))
\right\rfloor,
\]
则
\[
\boxed{
\#\{0\le j<N:e_j>H(N)\}\le1.
}
\]

这里不声称存在一个对所有 \(N\) 固定的全局异常索引。

## 4. 定理 F3-PEAK-3：反射定位与单峰剔除

设
\[
P=3^t.
\]
若已知一个索引 \(a\) 满足
\[
e_a\ge t,
\]
则另一个根类是
\[
b\equiv-a-AB^{-1}\pmod P,
\qquad0\le b<P,
\]
且
\[
\boxed{
\{j\ge0:e_j\ge t\}
=
\{j\equiv a\pmod P\}
\sqcup
\{j\equiv b\pmod P\}.
}
\]

令
\[
P=3^T.
\]
在完整区段 \(0\le j<P\) 中：
\[
\boxed{
\sum_{j<P}D_j-M_1(P)-M_2(P)
=
(2k+1)P-1-4k-2T.
}
\]

若进一步
\[
B=1
\]
即根迹为负整数，且
\[
3^T>A-3,
\]
则
\[
\boxed{
M_2(3^T)=2k+T.
}
\]

删除一个最大值后，剩余 \(3^T-1\) 项的完整直方图固定为
\[
\begin{array}{c|c}
D&\text{次数}\\ \hline
2k&3^{T-1}\\
2k+t,\ 1\le t<T&4\cdot3^{T-t-1}\\
2k+T&1.
\end{array}
\]

因此
\[
\boxed{
\sum_{j<3^T}D_j-M_1(3^T)
=
(2k+1)(3^T-1)-T.
}
\]

同时，对任意预先指定的高峰
\[
H>2k+T,
\]
存在显式普通整数参数使
\[
D_0=H
\]
而其余前 \(3^T\) 项最大值仍为
\[
2k+T.
\]

## 5. 定理 F3-PEAK-4：超临界峰的有效稀疏界

固定
\[
\theta>1.
\]
若两个正索引
\[
a<b
\]
都满足
\[
3^{e_j}>j^\theta,
\]
则
\[
\boxed{
b>
\frac{a^\theta-A}{B}-a.
}
\]

令
\[
\beta=\frac{\theta+1}{2}>1
\]
并取研究稿给出的显式 \(J_0\)。则
\[
\boxed{
\#\{J_0\le j<X:3^{e_j}>j^\theta\}
\le
1+
\left\lfloor
\frac{\log(\log X/\log J_0)}
{\log\beta}
\right\rfloor.
}
\]

即得到有效
\[
O(\log\log X)
\]
上界。

这个结论**不**推出超临界集合有限；前轮的最终有限性仍需要更深的 \(S\)-部分/Roth 型输入。

## 6. 边界

- 核心第二峰结论不替代最高峰的非有效 \(S\)-部分估计。
- 没有证明
  \[
  M_1(N)=2k+\log_3N+O(1).
  \]
- 没有新的固定间距素数计数。
- 任意高孤峰构造允许参数随目标高度变化。

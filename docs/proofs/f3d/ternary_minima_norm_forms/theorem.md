# F3D-TERN：三元最小值的 9–10–9 次数谱与范数形式

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3D-TERN-1\` 至 \`F3D-TERN-6\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源 | [f3d_ternary_minima_and_norm_forms.md](../../../f3_balance_research/f3d_ternary_minima_and_norm_forms.md) |
| 前置结果 | [F3D-DEG](../degree_tensorization/theorem.md) |
| Lean 状态 | 尚未形式化 |
| 外部背景 | 有限域范数形式；三元二次型在 \(\mathbf F_3\) 的非平凡零点（正文也给初等证明） |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

定义
\[
\mathfrak d_m(k)
=
\deg_F(k\min(t_1,\ldots,t_m)).
\]

## F3D-TERN-1：三输入 9–10–9 次数谱

对三个输入：
\[
\boxed{
\mathfrak d_3(k)=
\begin{cases}
9,&k=1,\\
10,&k=2,\\
3k,&k\ge3.
\end{cases}
}
\]

因此
\[
\boxed{
\mathfrak d_3(1)=9,\quad
\mathfrak d_3(2)=10,\quad
\mathfrak d_3(3)=9.
}
\]

两倍放大反而比三倍更贵。

## F3D-TERN-2：一倍最小值的小输入精确值

三输入一倍最小值由
\[
R_{3,1}(x,y,z)
=
\frac{H(x,y)+3z^3}{Q(x,y)+3z^2}
\]
九次实现，其中
\[
Q=x^2+y^2,\qquad
H=x^3-xy^2+y^3.
\]

四输入一倍最小值由两个二元无抵消块组合，得到
\[
\boxed{\mathfrak d_4(1)=12.}
\]

## F3D-TERN-3：两倍最小值的分母代价

三输入存在显式十次构造
\[
R_{3,2}(x,y,z)
=
\frac{A(x,y,z)}{x^2+y^2},
\]
其中
\[
A=(x^2+y^2)^2+x^2yz+(x^2+y^2)z^2.
\]

对全部非零有理 \(x,y,z\)：
\[
\boxed{
v_3(R_{3,2})
=
2\min(v_3(x),v_3(y),v_3(z)).
}
\]

更一般地，对 \(m\ge3\)：
\[
\boxed{
\mathfrak d_m(2)\ge2m+4.
}
\]

证明核心：

1. 任意实现可正规化成互素齐次 \(A/B\)，其中
   \[
   \deg_iA=\deg_iB+2.
   \]
2. 若 \(B\) 非常数，则每个依赖变量次数不是 1，而至少是 2；齐次性迫使它依赖至少两个变量，因此
   \[
   \sum_i\deg_iB\ge4.
   \]
3. 若 \(B\) 为常数，则得到一个三元以上齐次二次型，其模 \(3\) 必须在所有非零向量上非零；这不可能。正文给出三元二次型的初等对角化证明。

对 \(m=3\) 得下界 \(10\)，与显式构造吻合。

## F3D-TERN-4：三元三次范数形式

定义
\[
\mathcal N_3(x,y,z)
=
x^3+2x^2z-xy^2+3xyz+xz^2-y^3+yz^2+z^3.
\]
它是有限域扩张
\[
\mathbf F_{27}/\mathbf F_3
\]
的范数形式的整数提升，满足
\[
\boxed{
v_3(\mathcal N_3(x,y,z))
=
3\min(v_3(x),v_3(y),v_3(z)).
}
\]

从而三倍三输入最小值九次实现；截面下界也是九次，所以
\[
\boxed{\mathfrak d_3(3)=9.}
\]

## F3D-TERN-5：一般高增益范数公式

对每个 \(k\ge1\)，有限域范数给出 \(k\) 元 \(k\) 次无抵消形式。若 \(m\le k\)，把多余坐标设零可得
\[
N_{k,m}
\]
满足
\[
v_3(N_{k,m}(\mathbf x))
=
k\min_i v_3(x_i).
\]

因此对
\[
m\ge2,\qquad k\ge m
\]
有
\[
\boxed{
\mathfrak d_m(k)=mk.
}
\]

## F3D-TERN-6：任意输入数的一倍最小值上界

令
\[
r=\lceil\sqrt m\rceil,
\qquad
s=\lceil m/r\rceil\le r.
\]
把 \(m\) 个输入分成 \(s\) 组，每组至多 \(r\) 个。

每组分别用 \(r\) 次、\(r+1\) 次范数形式编码该组最小赋值，再用权重
\[
1,3,\ldots,3^{s-1}
\]
消除组间并列抵消。

得到
\[
\boxed{
3m
\le
\mathfrak d_m(1)
\le
m(\lceil\sqrt m\rceil+1).
}
\]

上界为
\[
O(m^{3/2}).
\]
对 \(m=2,3,4\) 与下界吻合；更大 \(m\) 不声明最优。

## 边界

- 次数是原整数数对的最大总次数，而不是比坐标有理式的形式总次数。
- \(m=3,k=2\) 的十次下界依赖“分母代价”而不仅是单输入截面。
- 有限域范数形式是经典工具；本包不把它作为新理论。
- 没有声称一般 \(m\) 的一倍最小值次数已经完全分类。

# F3D-DEG：独立缩放的次数张量化与最优双输入运算

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3D-DEG-1\` 至 \`F3D-DEG-6\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源研究稿 | [f3d_degree_tensorization.md](../../../f3_balance_research/f3d_degree_tensorization.md) |
| 前置结果 | [F3D-POLY](../polynomial_realization/theorem.md)、[F3D-MULTI](../multivariate_tropical/theorem.md) |
| Lean 状态 | 尚未形式化 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 次数

对全域可实现
\[
g:\mathbb Z^m\to\mathbb Z,
\]
定义
\[
\deg_F(g)
\]
为所有实现 \(g\) 的固定整数多项式对 \((P,Q)\) 的最小最大总次数。

不可实现时记为 \(+\infty\)。

## 2. 定理 F3D-DEG-1：放大取正部的精确最低次数

对每个
\[
k\ge2
\]
存在 \(k\) 次整数齐次多项式 \(H_k(u,v)\) 满足
\[
v_3(H_k(u,v))
=
k\min(v_3(u),v_3(v)).
\]

因此存在 \(k\) 次整数多项式对实现
\[
k\,t_+.
\]

结合正端斜率下界，
\[
\boxed{
\deg_F(k\,t_+)
=
\begin{cases}
3,&k=1,\\
k,&k\ge2.
\end{cases}
}
\]

所以数值放大并不使“单位输出复杂度”单调增加：单倍取正部需要 3 次，而二倍取正部只需 2 次。

## 3. 定理 F3D-DEG-2：独立输入次数下界可相加

对第 \(i\) 个坐标及其余坐标固定值 \(c\)，令单输入截面为
\[
g_{i,c}(t).
\]
定义
\[
\delta_i(g)
=
\sup_c\deg_F(g_{i,c}).
\]

若 \(g\) 全域可实现，则
\[
\boxed{
\deg_F(g)
\ge
\sum_{i=1}^m\delta_i(g).
}
\]

证明使用对每组输入变量的多齐次分解以及独立共同缩放
\[
X_i\mapsto3^{sw_i}X_i.
\]
这不是一般等号定理，而是统一下界。

## 4. 定理 F3D-DEG-3：有符号和的精确张量化

设一元 \(h\) 可实现，
\[
\epsilon_i\in\{\pm1\},
\qquad r\in\mathbb Z.
\]
则
\[
\boxed{
\deg_F
\left(
h\left(
\sum_{i=1}^m\epsilon_it_i+r
\right)
\right)
=
m\,\deg_F(h).
}
\]

下界来自 F3D-DEG-2；上界通过先用一个 \(m\) 次多齐次数对聚合全部带符号输入，再只应用一次最优齐次 \(h\) 实现。

## 5. 定理 F3D-DEG-4：双输入 min/max 的精确最低次数

对 \(p=3\)，
\[
\boxed{
\deg_F(\min(t,s))
=
\deg_F(\max(t,s))
=
6.
}
\]

更一般地，对
\[
k\ge2,
\]
\[
\boxed{
\deg_F(k\min(t,s))
=
\deg_F(k\max(t,s))
=
2k.
}
\]

合并为
\[
\boxed{
\deg_F(k\min(t,s))
=
\deg_F(k\max(t,s))
=
\begin{cases}
6,&k=1,\\
2k,&k\ge2.
\end{cases}
}
\]

特别地，
\[
2\min(t,s)
\]
和
\[
2\max(t,s)
\]
都有四次最优构造。

## 6. 定理 F3D-DEG-5：精确次数表与不可除法

研究稿中的精确最低次数包括：
\[
\deg_F(t\pm s)=2,
\]
\[
\deg_F(|t-s|)=4,
\]
\[
\deg_F(\mathbf1_{t>s})
=
\deg_F(\mathbf1_{t\ge s})
=
4,
\]
\[
\deg_F(\mathbf1_{t=s})=8.
\]

对任意固定符号 \(\epsilon_i\)：
\[
\deg_F
\left(
\left|
\sum_i\epsilon_it_i+r
\right|
\right)
=
2m,
\]
\[
\deg_F
\left(
\mathbf1_{\{\sum_i\epsilon_it_i>r\}}
\right)
=
2m,
\]
\[
\deg_F
\left(
\max\left(
\sum_i\epsilon_it_i+r,0
\right)
\right)
=
3m,
\]
\[
\deg_F
\left(
\mathbf1_{\{\sum_i\epsilon_it_i=r\}}
\right)
=
4m.
\]

此外，对任何
\[
k\ge2,
\]
不存在固定整数多项式对 \(T\)，即使只要求在
\[
F(X)\in k\mathbb Z
\]
的输入上，也不能全域满足
\[
F(T(X))=F(X)/k.
\]

所以“最后在 \(F\) 值外部除以 \(k\)”与“内部存在固定多项式除法器”是不同问题。

## 7. 定理 F3D-DEG-6：\(p=2\) 的精确层检测更低次

对 \(F_{2,D}\)，
\[
R_2(x)=
\frac{x^2+1}{x^2+x+1}
\]
满足
\[
\boxed{
v_2(R_2(x))
=
\mathbf1_{\{v_2(x)=0\}}.
}
\]

因此 \(p=2\) 的精确单位层检测最低次数为 2；相应双输入等值检测最低次数为 4。

对 \(p=3\)，这两个次数分别为 4 和 8。

这说明不同素数的**可实现函数类**相同，但某些函数的最优实现次数可以不同。

## 8. 边界

- 次数是原整数多项式数对的最大总次数，不是运算次数、系数位数或算法复杂度。
- 允许原实现非齐次。
- 下界要求输出只依赖输入 \(F\) 值并对全部单位部分/共同缩放成立。
- 本包不声称这些最优次数已有或没有文献先例；相邻 tropical complexity 文献不能直接替代这里的整数多项式总次数下界。

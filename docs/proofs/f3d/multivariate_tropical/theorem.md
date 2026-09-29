# F3D-MULTI：多输入固定多项式实现与整数热带表达式

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3D-MULTI-1\`、\`F3D-MULTI-2\`、\`F3D-MULTI-3\`、\`F3D-MULTI-4\` |
| 状态 | \`PAPER-AUDITED\` |
| 内容类型 | 正性检测；双输入最小/最大；批量最小值与第一极小位置；多输入完全分类；统一 Lipschitz 边界与条件开关不可实现性 |
| 整理日期 | 2026-09-29 |
| Lean 状态 | 尚未形式化；不属于 \`LEAN-PROVED\` |
| 外部依赖 | 三进赋值基本法则；有限 Lagrange 插值；分段线性/热带有理函数的标准表示背景 |

[PDF 版](paper.pdf) · [PDF 源](paper.tex) · [完整证明](proof.md) · [引理 DAG](scaffolding.md) · [形式化计划](formalization.md)

本包推广 [F3D-POLY](../polynomial_realization/theorem.md) 的单输入分类到任意固定有限输入数。

## 1. 定义

定义域
\[
\mathcal D=\{(n,d)\in\mathbb Z^2:n\ne\pm d\},
\]
并记
\[
F(n,d)=F_{3,D}(n,d)=v_3(n+d)-v_3(n-d).
\]

固定 \(m\ge1\)。若
\[
X_i=(n_i,d_i)\in\mathcal D,\qquad t_i=F(X_i),
\]
称整数多项式对
\[
(P,Q)\in
\mathbb Z[n_1,d_1,\ldots,n_m,d_m]^2
\]
**全域实现**
\[
g:\mathbb Z^m\to\mathbb Z
\]
若对全部 \(X_i\in\mathcal D\)：

1. \((P(\mathbf X),Q(\mathbf X))\in\mathcal D\)；
2.
   \[
   F(P(\mathbf X),Q(\mathbf X))
   =
   g(t_1,\ldots,t_m).
   \]

称一个函数是**有限整数热带表达式**，若它可由

- 整数常数；
- 坐标函数 \(t_i\)；
- \(+\)、\(-\)、\(\min\)、\(\max\)

有限次复合得到。

等价地，它可以写成
\[
\boxed{
g(\mathbf t)
=
\min_{1\le a\le A}
(c_a+\mathbf u_a\cdot\mathbf t)
-
\min_{1\le b\le B}
(d_b+\mathbf v_b\cdot\mathbf t),
}
\tag{T}
\]
其中
\[
c_a,d_b\in\mathbb Z,\qquad
\mathbf u_a,\mathbf v_b\in\mathbb Z^m.
\]

## 2. 定理 F3D-MULTI-1：二次正性检测

定义
\[
\boxed{
\Theta(n,d)
=
\left(
3n^2-2nd+3d^2,\,
(n-d)^2
\right).
}
\]
则对所有 \((n,d)\in\mathcal D\)，
\[
\boxed{
F(\Theta(n,d))
=
\mathbf1_{\{F(n,d)>0\}}.
}
\]
并且输出始终满足
\[
N>D>0.
\]

## 3. 定理 F3D-MULTI-2：最小值、最大值与第一极小位置

对非零有理数 \(x,y\)，定义
\[
\boxed{
\mu(x,y)=
\frac{x^3+3y^3}{x^2+3y^2}.
}
\]
则
\[
\boxed{
v_3(\mu(x,y))
=
\min(v_3(x),v_3(y)).
}
\]
因此
\[
\boxed{
v_3\!\left(\frac{xy}{\mu(x,y)}\right)
=
\max(v_3(x),v_3(y)).
}
\]

这些有理函数经清分母、齐次化和和差回代后，给出固定整数多项式对，实现两个输入的
\[
\min(F(X),F(Y)),
\qquad
\max(F(X),F(Y)).
\]

更一般地，对固定 \(m\ge1\) 和非零有理数
\[
x_0,\ldots,x_{m-1},
\]
定义
\[
H_k=\sum_{i=0}^{m-1}3^i x_i^k,
\qquad k\ge m.
\]
若
\[
a=\min_i v_3(x_i),
\qquad
i_0=\min\{i:v_3(x_i)=a\},
\]
则
\[
\boxed{
v_3(H_k)=ka+i_0.
}
\]
从而
\[
\boxed{
v_3\!\left(\frac{H_{m+1}}{H_m}\right)=a,
}
\]
以及
\[
\boxed{
v_3\!\left(
\frac{H_m^{m+1}}{H_{m+1}^{m}}
\right)=i_0.
}
\]

所以对于固定输入数 \(m\)，可以同时以固定多项式构造提取：

- 所有输入 \(F\) 值的最小值；
- 第一个达到最小值的输入编号。

## 4. 定理 F3D-MULTI-3：多输入完全分类

对固定 \(m\ge1\)，函数
\[
g:\mathbb Z^m\to\mathbb Z
\]
可由一个全域有效的固定整数多项式对实现，当且仅当 \(g\) 是有限整数热带表达式。

等价地，恰好是所有可以写成 (T) 的函数。

### 构造方向

在坐标
\[
x_i=\frac{n_i+d_i}{n_i-d_i}
\]
中，
\[
F(X_i)=v_3(x_i).
\]
以下赋值操作均有全域无零极点的固定有理函数实现：
\[
a+b,\quad a-b,\quad \min(a,b),\quad \max(a,b),\quad r\in\mathbb Z.
\]
有限复合后清分母、齐次化，即得到整数多项式对。

### 必要性

对任意固定全域多项式对，输出函数 \(g\) 在整数格点上具有有限整数仿射分区，且全部局部斜率来自有限集合。因此 \(g\) 可写成有限整数热带表达式。

证明中不忽略最低项抵消：使用一个固定有限单位网格和 Lagrange 插值，得到统一抵消深度上界，然后把剩余有限修正编码成有限个整数线性条件。

## 5. 定理 F3D-MULTI-4：统一 Lipschitz 边界与无界开关不可实现

任何可实现的
\[
g:\mathbb Z^m\to\mathbb Z
\]
都存在常数 \(L<\infty\)，使
\[
\boxed{
|g(\mathbf t)-g(\mathbf s)|
\le
L\|\mathbf t-\mathbf s\|_\infty
}
\]
对全部整数格点成立。

因此双输入函数
\[
\boxed{
G(t,s)=
\begin{cases}
s,&t\ge0,\\
0,&t<0
\end{cases}
}
\]
不可由一个全域固定整数多项式对实现，因为
\[
G(0,M)-G(-1,M)=M
\]
可以任意大，而输入距离恒为 \(1\)。

但对每个固定 \(B\ge0\)，截断开关
\[
G_B(t,s)
=
\begin{cases}
\max(-B,\min(s,B)),&t\ge0,\\
0,&t<0
\end{cases}
\]
可以实现。

一个显式热带表达式是
\[
H(t)=\mathbf1_{\{t\ge0\}}
=
\min(1,\max(0,t+1)),
\]
\[
G_B(t,s)
=
\min(s_+,BH(t))
-
\min((-s)_+,BH(t)).
\]

## 6. 素数 \(p\) 的普遍版本

最小值构造实际对任意素数 \(p\) 成立：
\[
\boxed{
v_p\!\left(
\frac{x^3+py^3}{x^2+py^2}
\right)
=
\min(v_p(x),v_p(y)).
}
\]
批量公式只需把 \(3^i\) 替换为 \(p^i\)。

因此多输入固定多项式表达结构本身不是 \(p=3\) 特有现象；\(F_3\) 在素数截面上的特殊性必须来自另外的模 \(3\) 算术结构。

## 7. 边界

- 分类的是固定整数系数多项式对的**全域**实现能力。
- 允许算法分支、循环、输入相关公式或只在有限集合/固定同余域上成立，超出本定理范围。
- 热带有理函数和分段线性函数的表示理论已有独立文献；本包不把一般 min/max 表示理论本身作为新发现。
- 当前尚未完成系统首创性查新。
- 本结果尚未进入 Lean。

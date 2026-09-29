# F3D-POLY：固定整数多项式对 \(F_{3,D}\) 的实现能力

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3D-POLY-1\`、\`F3D-POLY-2\`、\`F3D-POLY-3\`、\`F3D-POLY-4\` |
| 状态 | \`PAPER-AUDITED\` |
| 内容类型 | 四次精确层检测；固定整数多项式实现函数的完全分类；最低次数；不可实现性推论 |
| 整理日期 | 2026-09-29 |
| Lean 状态 | 尚未形式化；不属于 \`LEAN-PROVED\` |
| 外部依赖 | 三进赋值基本法则；Hensel 简单根提升；完备赋值域绝对值向有限代数扩张的唯一延拓 |

[PDF 版](paper.pdf) · [PDF 源](paper.tex) · [完整证明](proof.md) · [引理 DAG](scaffolding.md) · [形式化计划](formalization.md)

## 1. 定义

定义域
\[
\mathcal D=\{(n,d)\in\mathbb Z^2:n\ne d,\ n\ne-d\}.
\]
对 \((n,d)\in\mathcal D\)，令
\[
\boxed{
F(n,d):=F_{3,D}(n,d)=v_3(n+d)-v_3(n-d)\in\mathbb Z.
}
\]

这里 \(v_3\) 作用于非零整数；等价地，若
\[
x=\frac{n+d}{n-d}\in\mathbb Q^\times,
\]
则
\[
\boxed{F(n,d)=v_3(x).}
\]

称整数多项式对
\[
(P,Q)\in\mathbb Z[n,d]^2
\]
**全域实现**函数 \(g:\mathbb Z\to\mathbb Z\)，若对所有 \((n,d)\in\mathcal D\)：

1. \((P(n,d),Q(n,d))\in\mathcal D\)；
2. 
   \[
   F(P(n,d),Q(n,d))=g(F(n,d)).
   \]

定义该实现的次数为
\[
\deg(P,Q)=\max(\deg P,\deg Q).
\]

## 2. 定理 F3D-POLY-1：四次精确层检测

定义
\[
\boxed{
E_0(n,d)=
\left(
5n^4+22n^2d^2+5d^4,\,
(n^2-d^2)^2
\right).
}
\]
则对所有 \((n,d)\in\mathcal D\)，
\[
\boxed{
F(E_0(n,d))
=
\mathbf 1_{\{F(n,d)=0\}}.
}
\]

而且输出总满足
\[
N>D>0,
\]
其中 \(E_0(n,d)=(N,D)\)。

进一步，对任意固定整数 \(r\)，存在显式线性整数多项式对 \(S_r\) 满足
\[
F(S_r(n,d))=F(n,d)+r.
\]
于是
\[
E_r:=E_0\circ S_{-r}
\]
满足
\[
\boxed{
F(E_r(n,d))
=
\mathbf 1_{\{F(n,d)=r\}}.
}
\]
所有 \(E_r\) 仍为四次多项式对。

## 3. 定理 F3D-POLY-2：固定多项式实现函数的完全分类

设 \(g:\mathbb Z\to\mathbb Z\)。

存在一个全域有效的固定整数多项式对 \((P,Q)\) 实现 \(g\)，当且仅当存在整数
\[
a_+,b_+,a_-,b_-\in\mathbb Z
\]
和阈值 \(T_+,T_-\)，使
\[
g(t)=a_+t+b_+
\qquad(t\ge T_+),
\]
以及
\[
g(t)=a_-t+b_-
\qquad(t\le T_-).
\]

也就是说：

> **可由固定整数多项式对全域实现的 \(g\)，恰好是正负两端分别最终成为整数仿射函数的整数值函数。**

中间有限多个整数上的值可以任意指定。

### 显式构造

令
\[
(t-r)_+=\max(t-r,0)
\]
以及
\[
c_r=g(r+1)-2g(r)+g(r-1).
\]
因为 \(g\) 两端最终仿射，仅有限多个 \(c_r\ne0\)，并且
\[
g(t)=a_-t+b_-+\sum_r c_r(t-r)_+.
\]

定义
\[
\boxed{
\rho(x)=\frac{x(x^2+1)}{x^3-x+1}.
}
\]
则
\[
v_3(\rho(x))=\max(v_3(x),0)
\qquad(x\in\mathbb Q^\times).
\]

于是
\[
\boxed{
\mathcal R_g(x)
=
3^{b_-}x^{a_-}
\prod_{r:c_r\ne0}
\rho(3^{-r}x)^{c_r}
}
\]
满足
\[
v_3(\mathcal R_g(x))=g(v_3(x)).
\]

将 \(\mathcal R_g=A/B\) 清去有理系数分母、齐次化并换回
\[
u=n+d,\qquad v=n-d
\]
即可得到所需整数多项式对 \((P,Q)\)。

## 4. 定理 F3D-POLY-3：四个基础操作的最低次数

以下最低次数均按 \(\deg(P,Q)\) 计算。

| 目标函数 \(g(t)\) | 最低次数 | 一个实现 |
|---|---:|---|
| \(t+r\) | \(\boxed{1}\) | 线性伸缩 \(S_r\) |
| \(|t|\) | \(\boxed{2}\) | \(R(x)=x/(x^2+1)\) |
| \(\max(t,0)\) | \(\boxed{3}\) | \(R(x)=\rho(x)\) |
| \(\mathbf 1_{\{t=0\}}\) | \(\boxed{4}\) | \(R(x)=(x^4+x^2+1)/(x^4+1)\)，等价于 \(E_0\) |

其中后三项均指经过齐次化回到整数多项式对后的次数。

## 5. 推论 F3D-POLY-4：不可实现函数

以下函数不能由一个全域有效的固定整数多项式对实现：
\[
t\mapsto t^2,
\qquad
t\mapsto(-1)^t,
\qquad
t\mapsto\left\lfloor\frac t2\right\rfloor.
\]

更一般地，任何在正端或负端不最终成为整数仿射函数的 \(g\) 都不可实现。

此外，不存在一个全域有效的固定双输入整数多项式构造，能够对两个独立输入对 \(X,Y\) 恒满足
\[
F(\Phi(X,Y))=F(X)F(Y).
\]
否则令 \(Y=X\)，就会得到单输入函数 \(t\mapsto t^2\)，与分类定理矛盾。

## 6. 边界

- 本定理分类的是**固定整数多项式对**的全域表达能力，不是算法可计算性。
- 允许循环、条件分支、让公式依赖输入，或只要求在某个有限子域/剩余类上成立，都超出本定理范围。
- 四次检测器与分类定理尚未进入 Lean。
- 本包不声称一般 \(p\)-进赋值、有理函数热带化或 Hensel 理论本身新颖；当前只固化这个 \(F_{3,D}\) 实现问题的完整分类与次数边界。

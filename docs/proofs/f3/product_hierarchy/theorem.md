# F3-HIER：任意高阶的低次数刚性与总乘积分岔

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-HIER-1\`、\`F3-HIER-2\`、\`F3-HIER-3\` |
| 状态 | \`PAPER-AUDITED\` |
| 内容类型 | 任意阶固定形状、低次数单项式刚性、总乘积根分岔、全素数渐近、同主系数对照族 |
| 整理日期 | 2026-09-29 |
| Lean 状态 | 尚未形式化；不属于 \`LEAN-PROVED\` |
| 外部依赖 | Green–Tao 线性形式素数定理；\(q>3\) 时使用 Green–Tao / Green–Tao–Ziegler 完成的一般有限复杂度版本 |

[PDF 版](paper.pdf) · [PDF 源](paper.tex) · [完整证明](proof.md) · [引理 DAG](scaffolding.md) · [形式化计划](formalization.md)

本包固化研究提交 \`8e72a960892f53c499695d8dc2dae3ed8062bf1b\` 中的高阶层级结论。它严格推广已有的 F3-HI 三因子定理；旧证明包保留为 \(q=3\) 的短版本和历史接口。

## 1. 记号

对整数 \(m>1\)，定义
\[
F_3(m)=v_3(m+1)-v_3(m-1)\in\mathbb Z.
\]

固定整数
\[
k,s\ge1,\qquad q=3^s,\qquad b=k+s,\qquad M=3^b.
\]
令
\[
W=\prod_{\substack{\ell\le q\\ \ell\ {\rm prime},\ \ell\ne3}}\ell,
\]
以及
\[
(c_0,\ldots,c_{q-1})=(0,1,\ldots,q-2,q).
\]
定义
\[
h_i=MWc_i,\qquad p_i=n+h_id.
\]

令 \(\mathcal Q_{k,s}(X)\) 为满足
\[
X<n,d\le2X,\qquad F_3(n)=k,
\]
且
\[
d,p_0,\ldots,p_{q-1}
\]
全部为素数的参数对集合。记
\[
D(n,d)=F_3\!\left(\prod_{i=0}^{q-1}p_i\right).
\]

定义
\[
\begin{aligned}
\kappa_{k,s}:={}&
\frac4{3^{k+2}}
\left(\frac32\right)^{q+1}
\prod_{\substack{\ell\le q\\\ell\ne3,\ \ell\ {\rm prime}}}
\left(\frac{\ell}{\ell-1}\right)^{q-1}\\
&\times
\prod_{\substack{\ell>q\\\ell\ {\rm prime}}}
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}.
\end{aligned}
\]
该乘积收敛且 \(\kappa_{k,s}>0\)。

## 2. 定理 F3-HIER-1：任意阶低次数刚性与全素数深度律

对任意非负整数指数向量
\[
\mathbf e=(e_0,\ldots,e_{q-1}),
\qquad
1\le u:=\sum_i e_i<q,
\]
在 \(\mathcal Q_{k,s}(X)\) 中恒有
\[
\boxed{
F_3\!\left(\prod_i p_i^{e_i}\right)
=
(-1)^{u+1}\bigl(k+v_3(u)\bigr).
}
\tag{H1}
\]

特别地，所有非空真子集乘积的 \(F_3\) 数据完全固定；甚至允许重复因子后，所有总次数小于 \(q\) 的单项式 \(F_3\) 数据仍完全固定。

同时
\[
\boxed{
|\mathcal Q_{k,s}(X)|
=
(\kappa_{k,s}+o_{k,s}(1))
\frac{X^2}{(\log X)^{q+1}}.
}
\tag{H2}
\]

对每个固定整数 \(R\ge b\)，
\[
\boxed{
\#\{(n,d)\in\mathcal Q_{k,s}(X):D(n,d)=R\}
=
(\kappa_{k,s}w_b(R)+o_{k,s,R}(1))
\frac{X^2}{(\log X)^{q+1}},
}
\tag{H3}
\]
其中
\[
w_b(R)=
\begin{cases}
\dfrac12,&R=b,\\[2mm]
3^{-(R-b)},&R>b.
\end{cases}
\]

所以同一个固定形状对每个 \(R\ge k+s\) 都有无穷多个全素数实现；形状本身不随 \(R\) 改变。

### 九端点实例

当 \(k=1,s=2\) 时，
\[
q=9,\qquad M=27,\qquad W=70,
\]
故
\[
p_i=n+1890c_i d,\qquad(c_i)=(0,1,2,3,4,5,6,7,9).
\]
总次数 \(u=1,\ldots,8\) 的 \(F_3\) 值依次为
\[
1,-1,2,-1,1,-2,1,-1.
\]
九个端点有
\[
2^9-2=510
\]
个非空真子集乘积；允许重复因子后，总次数 \(1\) 到 \(8\) 的非空单项式共有
\[
\binom{17}{8}-1=24309
\]
个。它们的 \(F_3\) 全由 (H1) 固定，而九因子总乘积可以取任意 \(R\ge3\)。

## 3. 定理 F3-HIER-2：系数和控制最高阶“锁死/开放”

更一般地，固定 \(q=3^s\)、\(M=3^{k+s}\)，取任意 \(3\nmid W\) 和非负整数 \(c_0,\ldots,c_{q-1}\)，令
\[
p_i=n+MWc_id,\qquad C=\sum_i c_i.
\]
假设 \(F_3(n)=k\ge1\)。

则所有总次数 \(1\le u<q\) 的单项式仍满足 (H1)。

令
\[
A(n)=\frac{n^q+1}{M}.
\]
存在整数多项式 \(H_n(d)\)，使
\[
\prod_i p_i+1
=
M\,G_n(d),
\]
其中
\[
\boxed{
G_n(d)=A(n)+WCn^{q-1}d+MH_n(d).
}
\tag{H4}
\]

并且 \(A(n)\) 为三进单位。

- 若 \(3\mid C\)，则
  \[
  \boxed{
  F_3\!\left(\prod_i p_i\right)=k+s
  }
  \]
  对所有正整数 \(d\) 恒成立。

- 若 \(3\nmid C\)，则 \(G_n:\mathbb Z_3\to\mathbb Z_3\) 是等距双射，存在唯一单位根 \(d_*(n)\in\mathbb Z_3^\times\)，且
  \[
  \boxed{
  F_3\!\left(\prod_i p_i\right)
  =
  k+s+v_3(d-d_*(n)).
  }
  \tag{H5}
  \]

因此普通等差系数
\[
(0,1,\ldots,q-1)
\]
会锁死总深度，因为其和被 \(3\) 整除；把最后一个系数从 \(q-1\) 移到 \(q\)，系数和增加 \(1\)，全部低次数数据保持不变，而总深度开放出唯一无限根分支。

## 4. 推论 F3-HIER-3：不存在统一有限次数截断

给定任意固定次数上限 \(L\)，存在一个固定的全素数伸缩形状，使全部总次数不超过 \(L\) 的单项式 \(F_3\) 数据完全相同，而全端点乘积的 \(F_3\) 深度无界。

证明只需取 \(s\) 使
\[
3^s>L
\]
并应用 F3-HIER-1。

所以不存在一个与阶数无关的有限次数上限，使该上限以内的单项式 \(F_3\) 数据成为所有更高阶总乘积深度的充分坐标。

## 5. 同主系数的刚性对照族

定义普通形状
\[
\widetilde p_i=n+MWi\,d,\qquad0\le i<q,
\]
并对它施加与 \(\mathcal Q_{k,s}(X)\) 相同的参数盒、输入层和全部素性要求。

则
\[
|\widetilde{\mathcal Q}_{k,s}(X)|
=
(\kappa_{k,s}+o_{k,s}(1))
\frac{X^2}{(\log X)^{q+1}}.
\]

两族具有：

- 完全相同的所有总次数 \(<q\) 的单项式 \(F_3\) 数据；
- 完全相同的全素数计数主系数 \(\kappa_{k,s}\)；

但最高阶行为不同：
\[
D_{\rm ordinary}\equiv k+s,
\]
而末点移动族具有 (H3) 的无限几何尾。

## 6. 边界

- 本结果的步长 \(d\) 可变；固定 \(d\) 后线性部分变为一维仿射相关，本证明不再适用。
- \(q=3\) 的情形只需 Green–Tao 2010 中复杂度至多 \(2\) 的无条件结果；一般 \(q\) 使用完成后的有限复杂度理论。
- 有限实验只作为 sanity check，不承担无限命题的证明责任。
- 本包不声称“幂赋值”“简单根提升”或一般有限复杂度素数定理本身是新结果。
- 当前尚未完成系统首创性查新；\`PAPER-AUDITED\` 不等于 \`LEAN-PROVED\`。

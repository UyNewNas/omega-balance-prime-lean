# F3D-STABLE：四次区间检测与有限层集合的稳定次数

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3D-STABLE-1\` 至 \`F3D-STABLE-5\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源 | [f3d_interval_detectors_and_stable_degree.md](../../../f3_balance_research/f3d_interval_detectors_and_stable_degree.md) |
| 前置结果 | F3D-POLY、F3D-DEG 与放大检测器研究 |
| Lean 状态 | 尚未形式化 |
| 外部背景 | \(p\)-进射影弦距核；Hensel；有限剩余树线性代数 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 次数函数

固定素数 \(p\)。对整数函数
\[
g:\mathbb Z\to\mathbb Z,
\]
记
\[
\deg_p(g)
\]
为全域实现 \(g(F_{p,D})\) 的固定整数多项式对的最低最大总次数。

定义放大次数
\[
a_{p,g}(k)=\deg_p(kg),
\qquad k\ge1.
\]

对有限层集合
\[
S\subset\mathbb Z
\]
写
\[
a_{p,S}(k)=a_{p,\mathbf1_S}(k).
\]

## 2. F3D-STABLE-1：任意有限区间的四次检测

以下取 \(p=3\)。令
\[
u=n+d,\qquad v=n-d.
\]
固定
\[
L\ge1,\qquad q\in\{1,2\},
\]
定义
\[
A_{L,q}
=
(9u^2+3^qv^2)
(u^2+3^{2L-2}v^2),
\]
\[
B_{L,q}
=
(9u^2+v^2)
(u^2+3^{2L-2+q}v^2),
\]
\[
\mathcal I_{L,q}
=
(A_{L,q}+B_{L,q},A_{L,q}-B_{L,q}).
\]

则
\[
\boxed{
F_{3,D}(\mathcal I_{L,q}(n,d))
=
q\,\mathbf1_{\{0\le F_{3,D}(n,d)<L\}}.
}
\]

配合线性层平移，任意非空有限整数区间
\[
I=[a,a+L-1]
\]
都可四次检测。

而且四次最优：
\[
\boxed{
a_{3,I}(1)=a_{3,I}(2)=4.
}
\]

次数至多 \(3\) 的既约有理函数若两端输出为 \(0\)，其分子分母根只能集中在一个三进赋值层；因此不能支持长度 \(\ge2\) 的区间。单层情形再用模 \(3\) 的两个单位类和 Hensel 简单根提升排除。

## 3. 剩余类核矩阵

固定深度
\[
r\ge1.
\]
把
\[
\mathbf P^1(\mathbb Q_p)
\]
划分为深度 \(r\) 的射影剩余类，共
\[
N_r=(p+1)p^{r-1}
\]
个。

定义类间共同深度核矩阵
\[
(K_r)_{ij}
=
\min\{v_p(u_iv_j-u_jv_i),r\},
\]
对角线取 \(r\)。

令 \(P_j\) 是在同一个深度 \(j\) 类上取平均的嵌套投影，则
\[
K_r
=
\sum_{j=1}^r
p^{r-j}P_j.
\]

对
\[
\theta\ge0,
\]
定义
\[
\lambda_j(\theta)
=
\frac{p^{r-j+1}-1}{p-1}+\theta.
\]
则
\[
\boxed{
(K_r+\theta I)^{-1}
=
\lambda_r^{-1}I
-
\sum_{j=1}^{r-1}
(\lambda_{j+1}^{-1}-\lambda_j^{-1})P_j.
}
\]

特别令
\[
\tau=\frac1{p-1},
\qquad
M_r=K_r+\tau I.
\]
则 \(M_r\) 正定，\(M_r^{-1}\) 的非对角元非正，并且
\[
M_r\mathbf1
=
\frac{p^r}{p-1}\mathbf1.
\]

## 4. F3D-STABLE-2：两端最终常值函数的稳定次数

设
\[
g:\mathbb Z\to\mathbb Z
\]
在两端最终常值。取足够大的 \(r\)，使
\[
g(v_p(x))
\]
在每个深度 \(r\) 射影剩余类上恒定，得到向量
\[
\mathbf g\in\mathbb Z^{N_r}.
\]
令
\[
\bar g
=
\frac1{N_r}\sum_i g_i.
\]

则极限
\[
\boxed{
\sigma_p(g)
:=
\lim_{k\to\infty}
\frac{\deg_p(kg)}k
}
\]
存在，并且
\[
\boxed{
\sigma_p(g)
=
\frac12
\left\|
\left(K_r+\frac1{p-1}I\right)^{-1}
(\mathbf g-\bar g\mathbf1)
\right\|_1.
}
\]

右侧与足够大的 \(r\) 的选择无关。

### 下界机制

把任意候选既约有理实现分解为代数根贡献。每个代数根的射影弦距平均剖面都可写成
\[
M_r\mu_\alpha
\]
其中
\[
\mu_\alpha\ge0,
\qquad
\|\mu_\alpha\|_1\le1.
\]
因此次数 \(d\) 只能提供至多 \(d\) 单位的正权和 \(d\) 单位的负权，给出 \(\ell^1\) 下界。

### 上界机制

在有限剩余树上用二次无抵消形式实现核矩阵列；解有限有理线性方程并清分母，得到真正的齐次整数多项式乘积。继续细分剩余类后，构造代价收敛到上式下界。最后由
\[
a_{p,g}(k+\ell)
\le
a_{p,g}(k)+a_{p,g}(\ell)
\]
和 Fekete 型次可加论证，把子序列上界提升为全部 \(k\) 的极限。

## 5. F3D-STABLE-3：有限层集合的显式稳定代价

对有限
\[
S\subset\mathbb Z
\]
令
\[
g=\mathbf1_S.
\]
则
\[
\boxed{
\sigma_p(S)
=
\frac{2(p-1)^2}{p(p+1)}|S|
-
\frac{2(p-1)^3}{p(p+1)}
\sum_{\substack{i<j\\i,j\in S}}
p^{-(j-i)}.
}
\]

而且所有有限 \(k\) 都有统一下界
\[
\boxed{
a_{p,S}(k)
\ge
\lceil k\sigma_p(S)\rceil.
}
\]

对 \(p=3\)：
\[
\boxed{
\sigma_3(S)
=
\frac23|S|
-
\frac43
\sum_{i<j\in S}3^{-(j-i)}.
}
\]

所以两个检测层之间有指数衰减的“共享成本节省”。

## 6. F3D-STABLE-4：连续区间恰好最省

若
\[
S=[a,a+L-1],
\]
则
\[
\boxed{
\sigma_p(S)
=
\frac{2(p-1)}{p+1}(1-p^{-L}).
}
\]

特别地
\[
\boxed{
\sigma_3([a,a+L-1])
=
1-3^{-L}.
}
\]

对固定层数
\[
|S|=L,
\]
稳定代价满足
\[
\boxed{
\sigma_p(S)
\ge
\frac{2(p-1)}{p+1}(1-p^{-L}),
}
\]
当 \(L\ge2\) 时等号当且仅当 \(S\) 是连续整数区间。

也就是说，在检测同样数量的离散层时，**把这些层排成连续区间在高增益极限下最省次数**。

## 7. F3D-STABLE-5：阈值与有限构造器

阈值
\[
\mathbf1_{\{t\ge1\}}
\]
的稳定次数为
\[
\boxed{
\lim_{k\to\infty}
\frac{\deg_p(k\mathbf1_{\{t\ge1\}})}k
=
\frac{p-1}{p+1}.
}
\]

所以长有限区间的稳定代价
\[
\frac{2(p-1)}{p+1}(1-p^{-L})
\]
随 \(L\to\infty\) 趋向两个阈值边界代价之和。

此外，有限剩余树线性方程给出可复现的整数多项式构造器；其次数/增益比沿精度细分收敛到稳定值。这个构造给上界，不声称每个有限增益都恰好达到
\[
\lceil k\sigma_p(S)\rceil.
\]

## 8. 边界

- 稳定次数是
  \[
  k\to\infty
  \]
  的渐近次数/增益比，不是运行时间或系数位长。
- 区间长度 \(L\) 固定后再令增益 \(k\to\infty\)。
- 对一般两端最终常值 \(g\)，必须使用 \(\ell^1\) 矩阵公式；二值集合的二次型化简不能误用于一般带符号目标。
- 本包不声称每个有限 \(k\) 的取整下界都可达到。
- 射影弦距能量核已有标准文献；新增论证是它与固定整数多项式实现次数之间的容量公式。

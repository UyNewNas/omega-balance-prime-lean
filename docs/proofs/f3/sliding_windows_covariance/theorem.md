# F3-WIN：滑动窗口双峰容量、统一剔除律与平移协方差

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-WIN-1\` 至 \`F3-WIN-6\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源 | [F3_sliding_windows_and_covariance.md](../../../f3_balance_research/F3_sliding_windows_and_covariance.md) |
| Lean 状态 | 尚未形式化 |
| 外部依赖 | 核心结果为初等三进/剩余类证明；文献仅用于结式/GCD 背景定位 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 设置

固定 \(k\ge1\)、\(q=3^k\) 和普通整数 \(n,d>1\)，处在此前双根基础事件 \(E_k\)。令
\[
D_j=v_3(Q_j),\qquad e_j=D_j-2k,
\]
且
\[
G(X)=4d^2(X-r_0)(X-r_1).
\]

写
\[
\delta=r_1-r_0\in1+3\mathbb Z_3,
\qquad
c=\frac{d^2-1}{q^2}\in\mathbb Z_{>0}.
\]
则
\[
\delta^2=\frac{c}{d^2}.
\]

## F3-WIN-1：精确双峰容量

对 \(h\ge1\)，定义
\[
\kappa_{k,d}(h)
=
\max_{j\ge0}\min(e_j,e_{j+h}).
\]
则最大值存在，并且
\[
\boxed{
\kappa_{k,d}(h)
=
v_3\!\left(h(d^2h^2-c)\right).
}
\]

等价地：
\[
\kappa(h)=
\begin{cases}
v_3(h),&3\mid h,\\
v_3(d^2h^2-c),&3\nmid h.
\end{cases}
\]

它与起点参数 \(n\) 无关。对任意 \(b\ge1\)，还能实现
\[
e_j\ge\kappa(h)+b,\qquad e_{j+h}=\kappa(h).
\]

## F3-WIN-2：完整二点联合尾

固定 \(a,b\ge1\)、\(h\ge1\)，令
\[
P_h(a,b)
=
\lim_{N\to\infty}
\frac1N
\#\{0\le j<N:e_j\ge a,\ e_{j+h}\ge b\}.
\]

若
\[
\nu_h=
\begin{cases}
2,&3\mid h,\\
1,&3\nmid h,
\end{cases}
\]
则
\[
\boxed{
P_h(a,b)
=
\begin{cases}
\nu_h\,3^{-\max(a,b)},&
\min(a,b)\le\kappa(h),\\
0,&\min(a,b)>\kappa(h).
\end{cases}
}
\]

## F3-WIN-3：所有滑动窗口的最佳第二峰

对窗口
\[
[U,U+N),\qquad N\ge3,
\]
记最大、第二大深度为
\[
M_1(U,N),\qquad M_2(U,N).
\]
定义
\[
K_{k,d}(N)=\max_{1\le h<N}\kappa_{k,d}(h).
\]
则
\[
\boxed{
\max_{U\ge0}M_2(U,N)
=
2k+K_{k,d}(N).
}
\]

该最大值可达到，且
\[
K_{k,d}(N)
\le
\left\lfloor
\log_3(d^2(N-1)^2-c)
\right\rfloor.
\]

## F3-WIN-4：任意平移窗口的统一单峰剔除律

令
\[
L=\lfloor\log_3N\rfloor.
\]
则对全部 \(U\ge0\)：
\[
\boxed{
\sum_{U\le j<U+N}D_j-M_1(U,N)
=
(2k+1)(N-1)+O_d(\log N),
}
\]
且误差有显式上下界，常数对所有 \(U\) 统一。

更精确地，研究稿给出层计数误差 \(\Theta(U,N)\) 和第二峰修正 \(m_2-L\) 的完全公式。

## F3-WIN-5：平移协方差闭式

定义
\[
\mathcal C_{k,d}(h)
=
\lim_{N\to\infty}
\frac1N
\sum_{j<N}
(D_j-(2k+1))
(D_{j+h}-(2k+1)).
\]
则
\[
\boxed{
\mathcal C_{k,d}(h)=
\begin{cases}
1,&h=0,\\
1-2\cdot3^{-v_3(h)},&h\ne0,\ 3\mid h,\\
-3^{-\kappa_{k,d}(|h|)},&3\nmid h.
\end{cases}
}
\]

整数轨道的 Cesàro 极限通过有限周期截断 \(e_R=\min(e,R)\) 与 \(L^2\) 尾控制严格得到，不假设根数字随机。

## F3-WIN-6：协方差恢复 \(d\)，但不能恢复 \(n\)

固定 \(k\)，全部精确协方差值
\[
\{\mathcal C(h):h\ge1\}
\]
唯一决定普通正整数 \(d\)。

对 \(h\equiv1\pmod3\)，协方差给出
\[
v_3(h-\delta),
\]
从而逐位恢复 \(\delta\in1+3\mathbb Z_3\)，再由
\[
\boxed{
d=(1-q^2\delta^2)^{-1/2},
\qquad d\equiv1\pmod3
}
\]
恢复 \(d\)。

但同一 \(k,d\) 下不同合法 \(n\) 只使整个深度函数发生三进平移：
\[
e'(x)=e(x+\theta),
\]
所以所有平移不变有限模式密度和协方差完全相同。平均后相位信息 \(n\) 被消去。

## 结式关系

首一归一化二次式 \(f\) 满足
\[
\operatorname{Res}(f(X),f(X+h))
=
h^2(h^2-\delta^2).
\]
\(\kappa(h)\) 是
\[
\max_jv_3(\gcd(G(j),G(j+h))),
\]
在本分裂二次模型中可精确算出；一般结式理论只给上界。

## 边界

- 不是素数计数定理。
- 不宣称所有远隔位置独立；事实上
  \[
  \mathcal C(3^a)\to1.
  \]
- 有限长度经验协方差不能自动支持任意精度的参数反演。

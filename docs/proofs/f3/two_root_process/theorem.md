# F3-ROOT：平移乘积过程的双根坐标、联合律与反演

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-ROOT-1\`、\`F3-ROOT-2\`、\`F3-ROOT-3\`、\`F3-ROOT-4\` |
| 状态 | \`PAPER-AUDITED\` |
| 内容类型 | 二次平移乘积序列、双 Hensel 根、完整联合尾分布、有限精度反演、全素数实现与局部障碍 |
| 整理日期 | 2026-09-29 |
| Lean 状态 | 尚未形式化；不属于 \`LEAN-PROVED\` |
| 外部依赖 | Hensel 简单根提升；全素数扩展使用一般有限复杂度素数线性形式定理 |

[PDF 版](paper.pdf) · [PDF 源](paper.tex) · [完整证明](proof.md) · [引理 DAG](scaffolding.md) · [形式化计划](formalization.md)

## 1. 平移乘积过程

固定整数 \(k\ge1\)，令
\[
q=3^k.
\]
对正整数参数 \(n,d\) 定义
\[
a_j=n+2jqd,\qquad
b_j=n+(2jq+2)d,\qquad
Q_j=a_jb_j+1
\qquad(j\ge0).
\]
在以下基础分支上工作：
\[
E_k:
\qquad
d\equiv1\pmod3,\qquad
v_3(Q_0),v_3(Q_1)\ge2k+1.
\]
在 \(E_k\) 上自动有
\[
n\equiv2\pmod3,
\]
故
\[
a_j\equiv2,\qquad b_j\equiv1\pmod3.
\]
因此
\[
D_j:=F_3(a_jb_j)=v_3(Q_j)>0.
\]

## 2. 定理 F3-ROOT-1：第三组锁定与双根精确分解

对所有 \(E_k\) 中的整数参数，
\[
\boxed{
Q_2-2Q_1+Q_0=8q^2d^2
}
\]
且
\[
\boxed{
D_2=2k.
}
\]

更强地，在 \(\mathbb Z_3\) 中存在唯一的两个简单根
\[
r_0\in3\mathbb Z_3,\qquad
r_1\in1+3\mathbb Z_3
\]
使对全部整数 \(j\ge0\)
\[
\boxed{
Q_j=4q^2d^2(j-r_0)(j-r_1).
}
\tag{R1}
\]
因此
\[
\boxed{
D_j=2k+v_3(j-r_0)+v_3(j-r_1).
}
\tag{R2}
\]

写
\[
r_0=3Z_0,\qquad r_1=1+3Z_1,
\]
则得到三分支公式
\[
\boxed{
\begin{aligned}
D_{3u}&=2k+1+v_3(u-Z_0),\\
D_{3u+1}&=2k+1+v_3(u-Z_1),\\
D_{3u+2}&=2k.
\end{aligned}
}
\tag{R3}
\]

## 3. 定理 F3-ROOT-2：两个根的独立均匀坐标与完整联合律

在 \(E_k\subset\mathbb Z_3^2\) 上取归一化 Haar 测度。映射
\[
(n,d)\longmapsto(Z_0,Z_1)
\]
把该测度推送为 \(\mathbb Z_3^2\) 上的乘积 Haar 测度。

等价地，对每个 \(T\ge1\)，
\[
(Z_0\bmod3^T,Z_1\bmod3^T)
\]
等概率取遍全部 \(3^{2T}\) 个可能值。

特别地，令
\[
L=2k+1.
\]
规定有限组门槛
\[
D_{3u_i+c_i}\ge L+t_i,
\qquad
c_i\in\{0,1\},\quad t_i\ge0.
\]
对每个分支令
\[
T_c=\max(\{t_i:c_i=c\}\cup\{0\}).
\]
若同一分支中的同余要求
\[
u_i\equiv u_j
\pmod{3^{\min(t_i,t_j)}}
\]
全部相容，则
\[
\boxed{
\Pr(\text{全部门槛}\mid E_k)=3^{-(T_0+T_1)}.
}
\tag{R4}
\]
若不相容，则概率为 \(0\)。

索引 \(j\equiv2\pmod3\) 的第三分支恒满足 \(D_j=2k\)，所以任何要求它超过 \(2k\) 的事件概率均为 \(0\)。

此外，任意连续 \(3^T\) 个整数索引中，对 \(1\le t\le T\) 都有
\[
\boxed{
\#\{j:D_j\ge2k+t\}=2\cdot3^{T-t}.
}
\tag{R5}
\]

## 4. 定理 F3-ROOT-3：完整深度序列可逆恢复参数

完整序列
\[
(D_j)_{j\ge0}
\]
在固定 \(E_k\) 分支内唯一决定参数 \((n,d)\in\mathbb Z_3^2\)。

具体地，对每个 \(T\ge1\)，在
\[
0\le j<3^T
\]
中满足
\[
D_j\ge2k+T
\]
的恰有两个位置，它们分别给出
\[
r_0\bmod3^T,\qquad r_1\bmod3^T.
\]

令
\[
\sigma=r_0+r_1,\qquad
\delta=r_1-r_0.
\]
则
\[
\boxed{
d=(1-q^2\delta^2)^{-1/2},
\qquad
n=-d(1+q\sigma),
}
\tag{R6}
\]
其中平方根选择唯一的 \(d\equiv1\pmod3\) 分支。

反过来，任意
\[
r_0\in3\mathbb Z_3,\qquad r_1\in1+3\mathbb Z_3
\]
都由 (R6) 构造出 \(E_k\) 中唯一的 \((n,d)\)。

若根已恢复到模 \(3^T\)，则可恢复
\[
\boxed{
n\bmod3^{k+T},
\qquad
d\bmod3^{2k+T}.
}
\tag{R7}
\]

而且在已知 \(E_k\) 的前提下，逐位恢复两个根时每一位每个根最多测试两个候选，因此至多
\[
\boxed{4(T-1)}
\]
次自适应深度阈值查询即可达到 (R7) 的精度。这里不声称该查询复杂度最优。

## 5. 定理 F3-ROOT-4：六位置的模 \(5\) 障碍与七素数修复

取 \(k=1\)。前三组涉及六个位置
\[
n,\ n+2d,\ n+6d,\ n+8d,\ n+12d,\ n+14d.
\]
若这六个整数都大于 \(5\) 且全部为素数，则必有
\[
\boxed{5\mid d.}
\tag{R8}
\]
因此在基础条件 \(d\equiv1\pmod3\) 下，不能再同时要求 \(d\) 本身为素数。

令
\[
d=5r.
\]
考虑七个线性形式
\[
r,\quad
n,\quad n+10r,\quad n+30r,\quad n+40r,\quad n+60r,\quad n+70r.
\]
它们局部可容许、线性方向两两不同，因此一般有限复杂度素数线性形式定理给出
\[
\#\mathcal P(X)
=
(\mathfrak S+o(1))
\frac{X^2}{(\log X)^7}
\]
其中 \(\mathfrak S>0\)，\(\mathcal P(X)\) 表示 \(X<n,r\le2X\) 且上述七个数全为素数的参数集合。

在该全素数族中，
\[
\boxed{
\Pr\bigl((D_0,D_1,D_2)=(3,4,2)\bigr)
\longrightarrow
\frac2{729}.
}
\tag{R9}
\]
因此该七素数模式出现无穷多次。

一个有限见证是
\[
n=208049,\qquad r=47,\qquad d=235,
\]
此时
\[
208049,\ 208519,\ 209459,\ 209929,\ 210869,\ 211339
\]
连同 \(47\) 均为素数，且前三组深度为
\[
(3,4,2).
\]

## 6. 文献边界

- 二次多项式的 \(p\)-进赋值树与平方判别式产生两条无限分支的一般现象已有系统研究；本包不把“双分支本身”包装成新发现。
- 随机 \(p\)-进多项式根的分布和相关性也已有独立文献。
- 本包登记的是这个特定 \(F_3\) 平移乘积过程中的显式双根坐标、完整联合律、有限精度反演，以及与全素数局部障碍的衔接。
- 首创性与独立发表分量仍需单独查新。
- 本结果尚未进入 Lean。

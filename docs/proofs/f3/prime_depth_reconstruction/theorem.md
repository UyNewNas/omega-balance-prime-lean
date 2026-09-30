# F3-REC：共享根深度的有限观测证书与采样复杂度

| 字段 | 内容 |
|---|---|
| 结果 ID | \`F3-REC-1\` 至 \`F3-REC-5\` |
| 状态 | \`PAPER-AUDITED\` |
| 来源 | [prime_depth_reconstruction.md](../../../f3_balance_research/prime_depth_reconstruction.md) |
| Lean 状态 | 尚未形式化 |
| 前置模型 | 固定共享根深度模型与固定精度全素数分布 |

[PDF](paper.pdf) · [完整证明](proof.md) · [脚手架](scaffolding.md) · [形式化计划](formalization.md)

## 1. 模型

固定已知基础深度
\[
b\ge1
\]
以及不同的三进单位根
\[
\alpha_1,\ldots,\alpha_m
\]
并假设它们模 \(3\) 同余。定义
\[
R_i=v_3(d-\alpha_i),
\qquad
D_i=b+R_i,
\]
\[
L_{ij}=v_3(\alpha_i-\alpha_j).
\]

讨论的观测接口只给出若干带标签深度向量
\[
(R_1,\ldots,R_m),
\]
不直接给根、参数或偏移系数。

## 2. F3-REC-1：一次不等观测就是精确距离证书

对任意实际配置和 \(i\ne j\)：
\[
\boxed{
\min(R_i,R_j)\le L_{ij}.
}
\]

若
\[
R_i\ne R_j,
\]
则更强地
\[
\boxed{
L_{ij}=\min(R_i,R_j).
}
\]

因此第一次观察到某一对深度不相等时，就立即得到该对根距离的**确定性精确证书**；不会因为样本少而产生一个错误距离，只可能暂时没有证书。

若
\[
\Delta=R_i-R_j,
\qquad L=L_{ij},
\]
局部模型中精确有
\[
\boxed{
\Pr(\Delta=0)=1-3^{-L},
}
\]
\[
\boxed{
\Pr(\Delta=h)=3^{-(L+|h|)}
\qquad(h\ne0).
}
\]

所以
\[
\boxed{
\Pr(R_i\ne R_j)=3^{-L_{ij}}.
}
\]

条件化于不等事件后，
\[
\Pr(|\Delta|=h\mid \Delta\ne0)=2\cdot3^{-h},
\qquad h\ge1,
\]
且符号正负各半，与 \(L\) 无关。

## 3. F3-REC-2：无误判恢复算法与等待时间

算法：对每一对 \((i,j)\)，扫描观测向量；首次发现
\[
R_i\ne R_j
\]
时记录
\[
L_{ij}=\min(R_i,R_j).
\]
未发生不等的指标对保持“未知”。

若所有指标对都获得证书，就恢复完整距离矩阵，进而在共享根模型中恢复根簇树和全部精确联合深度概率。

局部独立采样下，单对证书等待时间 \(\tau_{ij}\) 为几何分布：
\[
\boxed{
\Pr(\tau_{ij}>T)
=
(1-3^{-L_{ij}})^T,
\qquad
\mathbb E\tau_{ij}=3^{L_{ij}}.
}
\]

令
\[
K=\max_{i\ne j}L_{ij},
\qquad
B_m=\binom m2,
\]
以及全矩阵停止时间
\[
\tau=\max_{i<j}\tau_{ij}.
\]
则
\[
\boxed{
\Pr(\tau>T)
\le
\min\{1,B_me^{-T3^{-K}}\},
}
\]
\[
\boxed{
\mathbb E\tau
\le
1+3^K(1+\log B_m).
}
\]

所以
\[
T\ge3^K\log(B_m/\delta)
\]
足以使完整恢复概率至少为 \(1-\delta\)。

对于固定形状的真实全素数集合，充分大 \(X\) 后同样有
\[
\Pr(\text{\(T\) 次后仍缺证书})
\le
B_me^{-T/(2\cdot3^K)}.
\]

这里独立性是“有放回地独立抽取完整配置”，不是一个配置内部各输出独立。

## 4. F3-REC-3：被动辨识的 \(3^L\) 样本下界

只看两个带标签输出。令
\[
\mu_L,\mu_{L+1}
\]
分别表示根距离指数为 \(L,L+1\) 的双输出局部分布。

则
\[
\boxed{
\|\mu_L-\mu_{L+1}\|_{\rm TV}
=
3^{-L}.
}
\]

任何使用 \(T\) 次独立完整深度观测、在这两个模型之间判断的算法，其两模型中较大的错误概率至少为
\[
\boxed{
\frac12(1-3^{-L})^T.
}
\]

因此若要求两边错误率都不超过
\[
\delta<1/2,
\]
必要有
\[
\boxed{
T
\ge
\frac{\log(1/(2\delta))}
{-\log(1-3^{-L})}
\ge
\frac23\,3^L\log(1/(2\delta)).
}
\]

所以被动观测的 \(3^L\) 样本尺度是正确量级；证书算法在阶数上不能普遍改进。

## 5. F3-REC-4：截断深度仍可精确恢复截断距离

固定
\[
H\ge1
\]
只观察
\[
Y_i=\min(R_i,H).
\]
目标改为
\[
L^{[H]}_{ij}=\min(L_{ij},H).
\]

若
\[
Y_i\ne Y_j,
\]
则
\[
L_{ij}=\min(Y_i,Y_j)<H.
\]

若
\[
Y_i=Y_j=H,
\]
则
\[
L_{ij}\ge H
\]
所以
\[
L^{[H]}_{ij}=H.
\]

只有
\[
Y_i=Y_j<H
\]
时本次观测不给该对新证书。

单次证书概率为
\[
\boxed{
\pi_H(L)=
\begin{cases}
3^{-L},&L<H,\\
1/(2\cdot3^{H-1}),&L\ge H.
\end{cases}
}
\]

于是
\[
\boxed{
\Pr(\text{\(T\) 次后未恢复全部截断距离})
\le
B_m
\exp\!\left(-\frac{T}{2\cdot3^{H-1}}\right).
}
\]

而任何两个满足
\[
L\ge H
\]
的双输出模型具有完全相同的截断观测分布，因此截断数据不能区分 \(L=H\) 与更大的真实距离。

## 6. F3-REC-5：三个等距根的精确停止时间

若
\[
m=3,
\qquad
L_{12}=L_{13}=L_{23}=L,
\]
则全矩阵证书停止时间满足
\[
\boxed{
\Pr(\tau>T)
=
3(1-3^{-L})^T
-
2\left(1-\frac32\,3^{-L}\right)^T.
}
\]

并且
\[
\boxed{
\mathbb E\tau
=
5\cdot3^{L-1}.
}
\]

证明来自三个根在共同模 \(3^L\) 父球中的三个下一层子球：进入两个不同子球后，全部三对距离都已有证书。

## 7. 边界

- 证书正确性是确定性的，不需要矩收敛或尾界。
- 等待时间概率才使用局部随机模型或固定精度全素数极限。
- 这是被动观测复杂度，不是主动查询复杂度。
- 已知偏移系数时可以直接计算 \(L_{ij}\)；本包研究的是只看深度记录时的独立恢复/核验。
- 恢复的是根间距离，不恢复根的绝对位置或整数参数。

## 2026-09-30 形式化覆盖补记

REC-L1/L2、单对REC-L4与REC-L11的确定性证书部分已通过代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b` 的完整Lean门禁；详见 [形式化映射](formalization.md)。这不标记本页含概率、等待时间、矩阵恢复或素数采样的全部主结果为LEAN-PROVED。纸面PAPER-AUDITED状态与局部内核覆盖分开记录。

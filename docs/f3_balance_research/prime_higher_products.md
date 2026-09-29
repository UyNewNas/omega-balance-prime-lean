# 素数伸缩族中二阶数据不变的三因子深度律

> 状态：研究档案。稳定定理、完整书面证明、引理 DAG 与形式化计划已经提升到
> [`docs/proofs/f3/higher_interactions/`](../proofs/f3/higher_interactions/theorem.md)。
> 本文件保留研究轮的原始组织方式，不作为 Lean 已证明声明。

对整数 (u>1)，定义
[
F_3(u)=v_3(u+1)-v_3(u-1).
]

固定 (kge1)，令
[
M=3^{k+1},qquad p_0=n,quad p_1=n+2Md,quad p_2=n+6Md.
]

研究轮的核心增量是：三个单点值与三个两两乘积值可以在同一个固定伸缩形状中全部锁定，而三因子乘积值仍可沿唯一三进根分支达到任意预先指定的高层；加入 (d,p_0,p_1,p_2) 全部为素数的要求后，这个自由度仍保留，并具有显式渐近分布。

完整、经过本轮整理和审计的版本见：

- [定理陈述](../proofs/f3/higher_interactions/theorem.md)
- [完整证明](../proofs/f3/higher_interactions/proof.md)
- [引理 DAG 与审计记录](../proofs/f3/higher_interactions/scaffolding.md)
- [形式化计划](../proofs/f3/higher_interactions/formalization.md)

原研究提交：`3dec39629b1bc3b032607b4c3e36b8410e535c75`。

本文件有意不重复整篇稳定证明，避免研究档和证明档未来发生内容漂移。

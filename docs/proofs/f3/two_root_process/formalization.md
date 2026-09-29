# F3-ROOT：形式化映射

数学状态：\`PAPER-AUDITED\`。Lean 状态：\`NOT-STARTED\`。

## 1. 推荐模块

- \`OmegaBalance/F3TwoRootLocal.lean\`
- \`OmegaBalance/F3TwoRootFinite.lean\`
- \`OmegaBalance/F3TwoRootPrime.lean\`

## 2. 目标接口

| 节点 | 建议 Lean 名称 | 状态 |
|---|---|---|
| ROOT-L1 | \`translatedPairQ_formula\` | 未实现 |
| ROOT-L3 | \`third_pair_depth_eq_two_mul\` | 未实现 |
| ROOT-L4 | \`normalizedPairPolynomial_mod_three\` | 未实现 |
| ROOT-L5 | \`translatedPair_two_roots\` | 未实现；需固定库 Hensel API |
| ROOT-L6 | \`translatedPair_depth_three_branches\` | 未实现 |
| ROOT-L7 | \`twoRoot_inverse_parameters\` | 未实现 |
| ROOT-L8 | \`twoRoot_parameters_equiv\` | 未实现 |
| ROOT-L11 | \`twoRoot_joint_tail_count_finite\` | 未实现 |
| ROOT-L12 | \`twoRoot_block_depth_count\` | 未实现 |
| ROOT-L13 | \`twoRoot_recover_parameters\` | 未实现 |
| ROOT-L14 | \`twoRoot_adaptive_query_bound\` | 未实现 |
| ROOT-L15 | \`six_positions_force_five_dvd_step\` | 未实现 |
| ROOT-L16 | \`seven_prime_system_admissible\` | 未实现 |
| F3-ROOT-4 prime asymptotic | \`seven_prime_twoRoot_pattern_asymptotic\` | \`BLOCKED-EXTERNAL\` |

## 3. 形式化策略

优先把概率陈述改写成有限模 \(3^T\) 的精确计数。这样：

- 不需要先搭建 Haar 测度理论；
- “独立均匀”可以表现为有限商上的显式双射；
- 联合尾公式直接成为 Finset cardinality；
- 之后若需要，再由 projective limit / Haar API 推出测度表述。

## 4. 三进反演

\(d=(1-q^2\delta^2)^{-1/2}\) 在 Lean 中不应先引入分析平方根黑箱。可先证明：

> 对每个有限精度 \(T\)，存在唯一 \(d\equiv1\pmod3\) 满足
> \[
> d^2(1-q^2\delta^2)\equiv1\pmod{3^T}.
> \]

用 Hensel/有限提升递归构造，再视需要接入 \(\mathbb Z_3\)。

## 5. Prime 层

七素数渐近依赖一般有限复杂度素数线性形式定理。不得以自定义 axiom 填充。

局部部分（模 \(2,3,5,\ell\ge7\)）可完全独立形式化。

## 6. PDF 与 Lean 状态

PDF 构建成功不改变 Lean 状态。

## 7. 验证登记

| 项目 | 状态 |
|---|---|
| 书面证明 | 完成 |
| 书面审计 | 完成 |
| PDF | workflow 生成 |
| 新增 Lean 声明 | 0 |
| Prime 主结论 kernel 验证 | 无 |

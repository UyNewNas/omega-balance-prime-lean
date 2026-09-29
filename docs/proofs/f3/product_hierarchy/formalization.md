# F3-HIER：形式化映射

数学状态：\`PAPER-AUDITED\`。Lean 状态：\`NOT-STARTED\`。

## 1. 推荐模块

- \`OmegaBalance/F3HierarchyLocal.lean\`
- \`OmegaBalance/F3HierarchyFinite.lean\`
- \`OmegaBalance/F3HierarchyPrime.lean\`

前两层不依赖 Green–Tao，可独立推进；Prime 层受外部深定理接口阻塞。

## 2. 目标声明

| 书面节点 | 建议 Lean 名称 | 状态 |
|---|---|---|
| HIER-L1 | \`v3_pow_signed_neighbor\` | 未实现 |
| HIER-L2 | \`f3_monomial_rigid_below_pow_three\` | 未实现 |
| HIER-L4 | \`f3_total_product_factor\` | 未实现 |
| HIER-L5 | \`f3_total_depth_rigid_of_coeffSum_dvd_three\` | 未实现 |
| HIER-L6 | \`f3_total_depth_root_coordinate\` | 未实现 |
| 有限根计数 | \`f3_total_root_count_mod_pow\` | 未实现 |
| 小素数局部可解 | \`f3_hierarchy_local_small_primes\` | 未实现 |
| 大素数局部计数 | \`f3_hierarchy_local_large_primes\` | 未实现 |
| F3-HIER-1 | \`f3_hierarchy_prime_distribution\` | \`BLOCKED-EXTERNAL\` |
| F3-HIER-2 | \`f3_hierarchy_coeffSum_dichotomy\` | 局部部分可先实现 |
| F3-HIER-3 | \`f3_no_uniform_finite_degree_cutoff\` | 主无穷性受外部依赖 |

## 3. 必须保留的语义

1. \(F_3\) 为 \(\mathbb Z\) 值差分。
2. 单项式指数允许重复因子。
3. \(q=3^s\) 且 \(s\ge1\)。
4. “总次数 \(<q\)”不能误写成“支持大小 \(<q\)”。
5. 根坐标 theorem 的前提必须包含 \(3\nmid\sum c_i\)。
6. 全素数 theorem 的 \(d\) 是变量素数；固定 \(d\) 不属于结论。
7. 一般 \(q\) 的 Prime 层不能只接 Green–Tao 2010 complexity-\(\le2\) 接口。

## 4. 外部依赖

不得用自定义公理模拟有限复杂度素数定理。若现有 Lean 库没有对应定理，主全素数结论保持 paper 状态。

## 5. PDF

\`paper.tex\` / \`paper.pdf\` 不改变 Lean 状态。

## 6. 验证登记

| 项目 | 状态 |
|---|---|
| 书面证明 | 完成 |
| 书面审计 | 完成 |
| PDF | workflow 生成 |
| 新增 Lean 声明 | 0 |
| 主定理 kernel 验证 | 无 |

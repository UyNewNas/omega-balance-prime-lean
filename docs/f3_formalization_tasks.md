# F₃ 全量形式化任务清单

此清单是周期性推进的持久化状态；只把精确提交实际通过内核与信任审计的结果登记为完成。纸面推导、数值核验与条件假设不替代 Lean 证明。

## 初始基线与并行边界

2026-09-24 首轮读取 AGENTS.md、README、深层覆盖说明与开放 issues/PR。
主分支起点：`d6ad217d6e09c418072ba3e7647b908d032c7892`（PR #4）。
PR #5 是独立的质因数求和工作，本轮不改动该分支。
固定 Lean 4.34.0 / mathlib `5ed2965256430c3649e86755f9576b54eca72435` 不变。
本地没有 Lean 工具链，且容器无法解析 github.com；使用 GitHub Actions 编译精确提交，不把源码检查当作内核核验。

## 总目标

| ID | 目标与前提 | 当前实现/依赖 | 状态 |
|---|---|---|---|
| INF-1 | 每个固定 k≥1，F₃=±k 的素数各有无穷多个 | F3Infinitude.lean；固定 mathlib 的 Dirichlet 自然数包装器 | 已内核核验，证据见下方 PR #6 |
| INF-2 | 全体素数数列中，连续两项的正→负、负→正转移各无穷次 | F3SignChanges.lean；显式无中间素数的 ConsecutivePrimes | 已内核核验，证据见下方 PR #6 |
| COR-1 | 固定 h≥0 的完整整数相关核 | 已有 F3Finite.lean；缺周期重叠计数、均方尾部界与极限传递 | 未完成 |
| COR-2 | 固定 r≥1 的均方近似周期 4/3^r | 依赖 COR-1；r=0 平移1不能套简式，需单独处理 | 未完成 |
| DEN-1 | 素数单点比例 3^(-k)、层级尾部 3^(1-K)，k,K≥1 固定 | 核验 ANT WeakPNT_AP 及加权→素数计数桥梁 | 未完成 |
| DEN-2 | 固定乘子的升层密度，含17的 1/2,1/3,1/9,... 条件分布 | DEN-1 与有限余数类计算；先完整核验真实声明 | 未完成 |
| LOG-1 | log₃-ad U 的收敛、同态、等距和 F₃ 连接 | 已有整数 U；需三进分析接口检索与补证 | 未完成 |
| RUN-1 | 固定 c≠0、L≥1 的全素数数列连续同值长串 | Shiu/Banks–Freiberg–Turnage-Butterbaugh；arXiv:1311.7003；需可审计形式化 | 未完成 |
| RUN-2 | 上述长串跨度有界版本，参数依赖明确 | RUN-1 的定量上游版本；不能替换成选取子序列的相邻性 | 未完成 |

## 第1轮：精确层级与无穷变号

工作分支 `feat/f3-infinitude-sign-changes`，[PR #6](https://github.com/UyNewNas/omega-balance-prime-lean/pull/6)。

### 实际证明

- `f3_prime_level_infinite`：任意整数 c≠0，集合 {p : p为素数、p>3、F₃(p)=c} 无限。
- `exists_prime_gt_f3_pos/neg`：对任意界限B及k≥1，产生超过B和3、取精确±k值的素数。
- `f3_prime_zero_level_empty`：零层在大于3的素数中为空，不能删除 c≠0 / k>0 前提。
- `exists_ordered_prime_opposite_levels`：超过任意界限存在有序精确相反层级的素数对；不限定距离。
- `f3_consecutive_pos_neg_infinite` 与 `f3_consecutive_neg_pos_infinite`：真正连续素数的两种符号转移，左端点集合分别无限。
- `f3_consecutive_sign_changes_infinite`：相邻素数的 F₃ 乘积为负发生无穷多次；不要求等幅。

### 依赖与边界

余数类 `3^k-1`、`3^k+1` 模 `3^(k+1)` 分别给出精确的正负层级。通过固定 mathlib 的
`Nat.forall_exists_prime_gt_and_modEq` 调用已证 Dirichlet 结果，其上游是
`Nat.infinite_setOfPred_prime_and_eq_mod`；未添加任何新的数学假设。

每个符号只选取一个足够的余数类，不声称它穷尽整个层级集合；新增 p=17 的反例回归守住这个边界。
连续变号通过首个异号素数及其前一个素数构造；`ConsecutivePrimes` 直接要求中间无素数。
新增 (7,11) 的回归证明说明相邻、异号仍不意味着间距2。

### 精确验证证据

- 首个代码提交 `c62c52502d79772cc746679d26d54467be88af8f`。
- 修复模数在商式中的归一化后，全部17条通用声明所在提交
  `9cf5b992cb669de95e5a655404f2a21d525d0433` 已通过
  [Lean CI #68](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35978249902)
  与 [Factor-sum #56](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35978249797)。
- 已核对 #68 的库构建、三组回归、公理审计、源码与一对一覆盖、有限检查步骤全部成功。
- 随后的两个新增回归及本清单整理，应以 PR #6 最终 head 的 CI 为准；最终精确 head、run 和合并提交登记在该 PR 的验证记录中，不能只沿用较早绿色状态。
- 本轮共新增17条通用定理/引理及2条回归，目标总审计覆盖209条，全部纳入 scripts/Audit.lean；没有改变门禁。

## 下一子任务

优先 COR-1 的有限周期重叠计数：模3^j与模3^k的条件相容当且仅当两个余数模3^min(j,k)相等；相容时，在模3^R的完整周期中（R≥max(j,k)）交集大小为3^(R-max(j,k))。先证这个可独立复用的有限定理，再接几何级数、均方尾部和极限。

当前没有第1项的数学输入阻塞。其余目标的缺口仍明确保留为分析/计数/上游形式化任务，不由本轮的 Dirichlet 无穷性替代。

停止规则：INF、COR、DEN、LOG、RUN 全部目标非空洞形式化并集成主分支，构建/回归/公理/源码/覆盖均通过后才结束；本轮不满足总停止条件。

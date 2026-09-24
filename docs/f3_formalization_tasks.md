# F₃ 全量形式化任务清单

此清单是周期性推进的持久化状态；只把精确提交实际通过内核与信任审计的结果登记为完成。纸面推导、数值核验与条件假设不替代 Lean 证明。

## 初始基线与并行边界

2026-09-24 首轮读取 AGENTS.md、README、深层覆盖说明与开放 issues/PR。
主分支起点：`d6ad217d6e09c418072ba3e7647b908d032c7892`（PR #4）。
PR #5 是独立的质因数求和工作，各轮不改动该分支。
固定 Lean 4.34.0 / mathlib `5ed2965256430c3649e86755f9576b54eca72435` 不变。
本地没有 Lean 工具链，且容器无法解析 github.com；使用 GitHub Actions 编译精确提交，不把源码检查当作内核核验。

## 总目标

| ID | 目标与前提 | 当前实现/依赖 | 状态 |
|---|---|---|---|
| INF-1 | 每个固定 k≥1，F₃=±k 的素数各有无穷多个 | F3Infinitude.lean；固定 mathlib 的 Dirichlet 自然数包装器 | 已完成并合入；PR #6 |
| INF-2 | 全体素数数列中，连续两项的正→负、负→正转移各无穷次 | F3SignChanges.lean；显式无中间素数的 ConsecutivePrimes | 已完成并合入；PR #6 |
| COR-1 | 固定 h≥0 的完整整数相关核 | F3Finite.lean + F3CorrelationFinite.lean；完整周期双余数重叠已证，尚缺截断相关求和、几何化简、均方尾部界与极限传递 | 进行中 |
| COR-2 | 固定 r≥1 的均方近似周期 4/3^r | 依赖 COR-1；r=0 平移1不能套简式，需单独处理 | 未完成 |
| DEN-1 | 素数单点比例 3^(-k)、层级尾部 3^(1-K)，k,K≥1 固定 | 核验 ANT WeakPNT_AP 及加权→素数计数桥梁 | 未完成 |
| DEN-2 | 固定乘子的升层密度，含17的 1/2,1/3,1/9,... 条件分布 | DEN-1 与有限余数类计算；先完整核验真实声明 | 未完成 |
| LOG-1 | log₃-ad U 的收敛、同态、等距和 F₃ 连接 | 已有整数 U；需三进分析接口检索与补证 | 未完成 |
| RUN-1 | 固定 c≠0、L≥1 的全素数数列连续同值长串 | Shiu/Banks–Freiberg–Turnage-Butterbaugh；arXiv:1311.7003；需可审计形式化 | 未完成 |
| RUN-2 | 上述长串跨度有界版本，参数依赖明确 | RUN-1 的定量上游版本；不能替换成选取子序列的相邻性 | 未完成 |

## 第1轮：精确层级与无穷变号

工作分支 `feat/f3-infinitude-sign-changes`，[PR #6](https://github.com/UyNewNas/omega-balance-prime-lean/pull/6)，已合入主分支提交 `007da90defc99dcf9fb92aad43a9d684ff99cb0b`。

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

- PR 最终 head `01a83e1787dea405514e660059a4d066f9861ce8`，文件树 `3e24c3b54669815a03808744048640f41ae9baf7`。
- [Lean CI #72](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35978792455) 与 [Factor-sum #60](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35978792468) 均成功。
- CI 日志：209 条 theorem/lemma 公理审计通过，只含标准 Lean 公理；19 个 Lean 文件无证明逃逸；209 条声明一对一审计覆盖；原有有限检查全部通过。

## 第2轮：完整周期的幂三余数重叠

工作分支 `feat/f3-correlation-finite-overlap`，[PR #7](https://github.com/UyNewNas/omega-balance-prime-lean/pull/7)。本轮只完成 COR-1 的一个有限基础层，不把它登记成完整相关极限定理。

### 实际证明

新增 `OmegaBalance/F3CorrelationFinite.lean`：

- `card_filter_range_modEq_pow_three`：若 `k ≤ R`，任意一个模 `3^k` 的余数类在 `0,…,3^R-1` 中恰出现 `3^(R-k)` 次。
- `modPairCount_eq_of_le`：若 `j ≤ k ≤ R`，条件 `n ≡ a (mod 3^j)` 与 `n ≡ b (mod 3^k)` 相容当且仅当 `a ≡ b (mod 3^j)`；相容时完整周期交集大小是 `3^(R-k)`，否则为0。
- `modPairCount_eq`：对任意 `j,k ≤ R`，
  ```math
  \#\{0\le n<3^R:n\equiv a\pmod{3^j},\ n\equiv b\pmod{3^k}\}
  =\begin{cases}
  3^{R-\max(j,k)},&a\equiv b\pmod{3^{\min(j,k)}},\\
  0,&\text{否则}.
  \end{cases}
  ```

这里复用固定 mathlib 的 `Nat.count_modEq_card`、`Nat.ModEq.of_dvd`、`Nat.pow_div`；没有引入中国剩余定理公理或手写计数假设。

### 边界与失败修复

首次 CI #78 只在空 Finset 的 theorem 名称上失败：使用了不存在的 `Finset.not_mem_empty`。修为固定版本实际接口 `Finset.notMem_empty` 后，数学证明本身无需改写。当前仍保留少量非失败型 deprecated/linter 警告，不计作证明失败。

### 已验证的代码 head

提交 `e9563d557e3e95603b3aad5b264b52dea7329698`，文件树 `c7c0014dfa5f1815df954c3164ec28f969881c10`：

- [Lean CI #80](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35983633665)：SUCCESS。库构建、三组回归、公理、源码、审计覆盖、有限检查均成功。
- [Factor-sum #68](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/35983633932)：SUCCESS，确认未破坏并行质因数求和门禁。
- `Axiom audit PASS: 212 declarations; only standard Lean axioms.`
- `Source audit PASS: 20 Lean files, no proof escapes.`
- `Audit coverage PASS: all 212 project theorem declarations covered exactly once.`
- 原有 144,240 项有限检查与 11 组边界测试重新通过。

本节文档提交后的最终 PR head 还需重新通过同样门禁，方可合入；不能把上述较早绿色 head 自动等同于最终文档 head。

## 下一子任务

继续 COR-1：利用 `modPairCount_eq` 展开一个完整 `3^R` 周期内的 `F₃,R(n)F₃,R(n+h)`，得到有限双重和；随后把“相容条件”化为关于 `3^min(j,k) | h,h-2,h+2` 的四项组合，并完成有限几何级数化简。之后才进入均方尾部界和极限交换。

需要特别保留符号方向：四项展开最终应趋向
`|h-2|₃ + |h+2|₃ - 2|h|₃`；有限重叠和本身不是这个无限极限。

其余 DEN、LOG、RUN 缺口保持不变，不由有限余数计数替代。

停止规则：INF、COR、DEN、LOG、RUN 全部目标非空洞形式化并集成主分支，构建/回归/公理/源码/覆盖均通过后才结束；当前不满足总停止条件。

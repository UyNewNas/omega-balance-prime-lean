# FΣ 质因数和左右平衡：形式化 theorem atlas

本清单固定本项目在 2026-09-24 已讨论的形式化范围；后续轮次只更新状态、Lean 声明、验证提交与阻塞，不自动把新研究问题加入停止条件。

状态约定：

- **VERIFIED**：声明源码存在，并且对应精确提交的完整 Lean 工作流（构建、回归、公理审计、覆盖审计）成功。
- **SOURCE**：源码已存在，但当前 PR 的最新精确提交尚未完成完整 Lean 验证；不能当作已验收。
- **PARTIAL**：已有核心接口，但本条固定范围仍缺至少一个公开结论或输入边界。
- **OPEN**：尚无对应 Lean 接口。
- **EXTERNAL-INPUT**：只要求把外部解析定理作为显式前提传递，不要求本仓库重新证明该外部定理。

所有 Ω 均按重数计；`omegaSum p = Ω(p-1)+Ω(p+1)`，绝不表示质因数求和。`primeFactorSum n = n.primeFactorsList.sum`；所有有符号差先转 `ℤ`。

| # | 数学目标 | Lean 声明 / 模块 | 当前状态 | 证明或来源边界 |
|---|---|---|---|---|
| 1.1 | `S(0)=S(1)=0`，素数、素数幂、非零乘法完全可加性 | `primeFactorSum_zero`, `primeFactorSum_one`, `primeFactorSum_prime`, `primeFactorSum_prime_pow`, `primeFactorSum_mul` | SOURCE | mathlib `primeFactorsList` |
| 1.2 | `FΣ(n)=0 ↔ S(n-1)=S(n+1)`；奇中心约去公共因子 2 | `primeFactorSumDiff_eq_zero_iff`, `primeFactorSumDiff_eq_half_diff`, `primeFactorSumBalanced_iff_half` | SOURCE | 纯代数/因子表 |
| 1.3 | 缺陷 `D(n)=n-S(n)`；`S(n)≤n`；正整数等号 iff 素数或 4 | `primeFactorDefect`, `primeFactorSum_le`, `primeFactorSum_eq_self_iff`, `primeFactorDefect_eq_zero_iff` | SOURCE | `FactorSumArithmetic` |
| 1.4 | 平衡相邻对含素数时只能 `(5,6)`；除中心 11 外两半均合数 | 现有 `prime_consecutive_sum_bound` 只给素数项 `≤5` | PARTIAL | 需补公开精确分类/中心推论 |
| 2.1 | Pomerance 余因子构造与缺陷公式 | `primeFactorSum_cofactor_construction`, `primeFactorSum_cofactor_defect` | SOURCE | 公式归属 Pomerance (2002)；不宣称首创 |
| 2.2 | 反解 `(B-A)r=1+Ad`, `(B-A)q=1+Bd` 与邻接+`q-r=d` 的可逆性 | `sumCofactor_inverse_identity`, `sumCofactor_inverse_iff` | SOURCE | `A≠B` 显式保留 |
| 2.3 | 互素、分母整除、符号和奇偶必要条件、反向恢复中心 | `sumCofactor_coprime`, `sumCofactor_ne`, `sumCofactor_divisibility`, `sumCofactor_sign`, `sumCofactor_opposite_parity`, `sumCofactor_even_sum_difference`, `sumCofactor_recover_balanced` | SOURCE | `FactorSumCofactor`; 最新 CI 待验 |
| 3.1 | 五表达式族及邻接/中心/左右分解恒等式 | `sumFamilyU/V/Q/R/Center`, `sumFamily_adjacent`, `sumFamily_center_eq`, `sumFamily_pred`, `sumFamily_succ` | SOURCE | 纯环恒等式 |
| 3.2 | 五项素数 ⇒ S 平衡素数、左右 Ω=5/4、`TΩ=9` | `SumFamilyPrimeValues`, `sumFamily_five_primes`, `sumFamily_left_profile`, `sumFamily_right_profile`, `sumFamily_omegaSum_eq_nine` | SOURCE | 素性全部为显式前提 |
| 3.3 | 仅 U,V 素数时 `FΣ(P)=D(Q)-D(R)`，以及缺陷相等 iff 平衡 | `sumFamily_defect_identity`, `sumFamily_balanced_iff_defect` | SOURCE | Q,R 可合数 |
| 3.4 | 显式 `A=15U,B=2V,d=13t+1,q=1+Bd,r=1+Ad,B-A=1` 接口 | 目前由族定义和邻接恒等式隐含，缺命名公开定理 | PARTIAL | 需补精确公式接口 |
| 4.1 | 无固定素因子：模 2,3,5,7 表 + `ℓ≥11` 总次数 9 根数界 | 无 Lean 模块 | OPEN | 第二轮笔记已有数学论证 |
| 4.2 | 五项不可约：两二次判别式 `30124,25665` 非平方；三次中心模 19 无根 | 无 Lean 模块 | OPEN | 第二轮笔记 |
| 4.3 | `P(t)` 严格增长 | `sumFamilyCenter_strictMono` | SOURCE | 自然参数 |
| 4.4 | Schinzel H 作为显式命题前提，推出本族无穷参数 | 目前只有 `infinite_sumFamily_implies_level_nine`，输入已经是“参数集合无限” | PARTIAL | 不把 H 加为公理；需建条件接口与局部相容/不可约桥接 |
| 4.5 | 经典 Nelson–Penney–Pomerance 族加入中心素性后的模 3 障碍 | 无 Lean 声明 | OPEN | 第二轮笔记 |
| 5.1 | Pomerance Ruth–Aaron 计数上界 ⇒ 本问题计数上界 | 无 Lean 传递接口 | EXTERNAL-INPUT | 外部解析定理本身不要求本仓库重证 |
| 5.2 | 计数上界 ⇒ 相对素数密度趋零、倒数和收敛 | 无 Lean 传递接口 | EXTERNAL-INPUT | 必须把解析输入边界写在定理类型中 |
| 6.1 | `S(n)≡Ω(n)-v₂(n) (mod 2)` | `primeFactorSum_parity`（等价写成 `S+v₂≡Ω`） | SOURCE | `FactorSumArithmetic` |
| 6.2 | S 平衡 ⇒ Ω 差与 `v₂` 差同奇偶 | `sumBalanced_count_valuation_parity` | SOURCE | 有符号差在 `ℤ` |
| 6.3 | 双平衡 ⇒ `p≡1,7 (mod 8)` | `doubleBalanced_mod_eight` | SOURCE | 必要条件 |
| 6.4 | 双平衡时高 `v₂` 为奇数且 ≥3；共同 S 值 `≡k-1 (mod2)` | 尚缺独立公开声明 | PARTIAL | 可由 6.1 + 模 8 结构推出 |
| 7.1 | 任意 S 平衡素数且 `TΩ≤8` iff `p∈{11,17,31}` | `sumBalanced_low_count_bound`, `small_sum_balanced_low_count`, `sumBalanced_total_le_eight_iff` | SOURCE | 先无限范围排除至 `<2000`，再内核证书；不是扫描替代证明 |
| 7.2 | `(2,3),(2,4),(3,3)` 三种半邻数形状及合数中心例外路径 | `sumPair_two_three_bound`, `sumPair_two_four_bound`, `sumPair_three_three_impossible` | SOURCE | 155、1897 由最终内核目录排除中心素性；可再补命名回归 |
| 7.3 | 三例之外 `TΩ≥9` | `sumBalanced_total_ge_nine`, `infinite_sumBalanced_level_ge_nine` | SOURCE | 完整分类推论 |
| 7.4 | 双平衡共同级数 `k≥5` | `doubleBalanced_level_ge_five` | SOURCE | 另有独立结构证明 |
| 8.1 | 五级实例 `870404071`，两边分解、共同 S=20936、中心及因子素性 | `doubleBalanced_870404071` | SOURCE | `norm_num`/Lean 内核素性；尚缺共同 S=20936 的命名 profile 定理 |
| 8.2 | 另一个五级实例 `748465063` | `doubleBalanced_748465063` | SOURCE | 不宣称数值最小 |
| 8.3 | 可达最小共同级数恰为 5 | `doubleBalanced_minimum_level` | SOURCE | 存在性 + 下界 |
| 8.4 | 原五项族 `t=5,41529,48465` 的三个中心与第三轮其他回归证书 | 仅 `t=5` 有 `sumFamily_prime_values_five`; 其余未全部入 Lean | PARTIAL | Python/Pocklington 不得冒充内核证明 |
| 9.1 | 五级完整形状 `{p-1,p+1}={6bcd,8rs}` 与 `r+s=b+c+d-1` | `HasDoubleFiveShape`, `doubleBalanced_five_has_shape`, `doubleBalanced_five_shape_iff` | SOURCE | 重复素因子允许 |
| 9.2 | 邻接绝对值式 `|4rs-3bcd|=1` | 由形状中的 `p±1` 隐含，缺独立公开式 | PARTIAL | 需补 signed/abs 形式 |
| 9.3 | 必要模 48 余数 7/41 | `doubleBalanced_five_mod_forty_eight` | SOURCE | 必要非充分 |
| 9.4 | 两个五级双平衡不能互为孪生；双平衡孪生共同级数 ≥6 | `doubleBalanced_five_not_twins`, `doubleBalanced_twins_level_ge_six` | SOURCE | 不宣称双平衡孪生存在 |
| 9.5 | 因数对方程及恢复 `K=3bc,L=b+c-1` | `doubleFactorPair_identity`, `doubleFactorPair_iff`, `doubleFactorPair_recover` | PARTIAL | 代数式已有；仍缺从 `b,c,x,y` 到完整五级素数中心的公开构造接口 |
| 10.1 | “任何无限固定总计数层都 ≥9” | `infinite_sumBalanced_level_ge_nine` | SOURCE | 无条件有限分类推论 |
| 10.2 | “若五项族参数无限，则存在无限多个 `TΩ=9` S 平衡素数” | `infinite_sumFamily_implies_level_nine` | SOURCE | 输入显式为参数集合无限 |
| 10.3 | Schinzel H 下最小可无穷出现固定总计数恰为 9 | 尚缺 H→参数无限桥接，因此整条仍未完成 | PARTIAL | 必须保持条件性 |

## 当前停止条件

只有当上表所有 **有效** 条目均转为 VERIFIED，所有 `EXTERNAL-INPUT` 条目已有清楚的“以外部输入为前提”的 Lean 传递定理，最终 PR 合入 `master`，并且最终 `master` 精确提交的 Lean CI 成功，才满足任务停止条件。

若后续发现某条数学陈述错误，应在本表保留原条目并改为 **REFUTED**，附反例和替代陈述；不得静默弱化。

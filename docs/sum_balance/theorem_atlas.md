# FΣ 质因数和左右平衡：形式化 theorem atlas

本清单固定本项目在 2026-09-24 已讨论的形式化范围；后续轮次只更新状态、Lean 声明、验证提交与阻塞，不自动把新研究问题加入停止条件。

状态约定：

- **VERIFIED**：声明源码存在，并且对应精确提交的完整 Lean 工作流（构建、回归、公理审计、覆盖审计）成功。
- **SOURCE**：源码已存在，但当前 PR 的最新精确提交尚未完成完整 Lean 验证；不能当作已验收。
- **PARTIAL**：已有核心接口，但本条固定范围仍缺至少一个公开结论或输入边界。
- **OPEN**：尚无对应 Lean 接口。
- **EXTERNAL-INPUT**：只要求把外部解析定理作为显式前提传递，不要求本仓库重新证明该外部定理。

所有 Ω 均按重数计；`omegaSum p = Ω(p-1)+Ω(p+1)`，绝不表示质因数求和。`primeFactorSum n = n.primeFactorsList.sum`；所有有符号差先转 `ℤ`。

FΣ 源码内核基线：`e95b7789a72dfaa0b616e6f482a542f4355ba522`。该精确提交的 `Lean` 工作流 `36034598834` 与 `Factor-sum verification` 工作流 `36034598813` 均成功；构建、回归、公理审计和声明覆盖审计通过。下列 38 条固定范围声明均由该分支基线核验；与最新 `master` 的集成仍须在合并提交上再次通过 CI。

| # | 数学目标 | Lean 声明 / 模块 | 当前状态 | 证明或来源边界 |
|---|---|---|---|---|
| 1.1 | `S(0)=S(1)=0`，素数、素数幂、非零乘法完全可加性 | `primeFactorSum_zero`, `primeFactorSum_one`, `primeFactorSum_prime`, `primeFactorSum_prime_pow`, `primeFactorSum_mul` | VERIFIED | mathlib `primeFactorsList` |
| 1.2 | `FΣ(n)=0 ↔ S(n-1)=S(n+1)`；奇中心约去公共因子 2 | `primeFactorSumDiff_eq_zero_iff`, `primeFactorSumDiff_eq_half_diff`, `primeFactorSumBalanced_iff_half` | VERIFIED | 纯代数/因子表 |
| 1.3 | 缺陷 `D(n)=n-S(n)`；`S(n)≤n`；正整数等号 iff 素数或 4 | `primeFactorDefect`, `primeFactorSum_le`, `primeFactorSum_eq_self_iff`, `primeFactorDefect_eq_zero_iff` | VERIFIED | `FactorSumArithmetic` |
| 1.4 | 平衡相邻对含素数时只能 `(5,6)`；除中心 11 外两半均合数 | `prime_consecutive_sum_eq_five_six`, `sumBalanced_halves_nonprime_of_ne_eleven` | VERIFIED | `FactorSumLowAux`，无限范围不等式而非有限扫描 |
| 2.1 | Pomerance 余因子构造与缺陷公式 | `primeFactorSum_cofactor_construction`, `primeFactorSum_cofactor_defect` | VERIFIED | 公式归属 Pomerance (2002)；不宣称首创 |
| 2.2 | 反解 `(B-A)r=1+Ad`, `(B-A)q=1+Bd` 与邻接+`q-r=d` 的可逆性 | `sumCofactor_inverse_identity`, `sumCofactor_inverse_iff` | VERIFIED | 全部在 `ℤ` 中；分母不被非法约掉 |
| 2.3 | 互素、分母非零/整除、符号和奇偶必要条件、反向恢复中心 | `sumCofactor_coprime`, `sumCofactor_ne`, `sumCofactor_divisibility`, `sumCofactor_sign`, `sumCofactor_opposite_parity`, `sumCofactor_even_sum_difference`, `sumCofactor_recover_balanced` | VERIFIED | `FactorSumCofactor`; 前提显式保留 |
| 3.1 | 五表达式族及邻接/中心/左右分解恒等式 | `sumFamilyU/V/Q/R/Center`, `sumFamily_adjacent`, `sumFamily_center_eq`, `sumFamily_pred`, `sumFamily_succ` | VERIFIED | 纯环恒等式 |
| 3.2 | 五项素数 ⇒ S 平衡素数、左右 Ω=5/4、`TΩ=9` | `SumFamilyPrimeValues`, `sumFamily_five_primes`, `sumFamily_left_profile`, `sumFamily_right_profile`, `sumFamily_omegaSum_eq_nine` | VERIFIED | 素性全部为显式前提 |
| 3.3 | 仅 U,V 素数时 `FΣ(P)=D(Q)-D(R)`，以及缺陷相等 iff 平衡 | `sumFamily_defect_identity`, `sumFamily_balanced_iff_defect` | VERIFIED | Q,R 可合数 |
| 3.4 | 显式 `A=15U,B=2V,d=13t+1,q=1+Bd,r=1+Ad,B-A=1` 接口 | `sumFamilyA/B/D`, `sumFamily_B_eq_A_add_one`, `sumFamily_B_sub_A_eq_one`, `sumFamily_Q_inverse`, `sumFamily_R_inverse`, `sumFamily_Q_sub_R` | VERIFIED | 除法自由的反解公式 |
| 4.1 | 无固定素因子：模 2,3,5,7 表 + `ℓ≥11` 总次数 9 根数界 | `sumFamily_mod_two_table`, `sumFamily_mod_three_table`, `sumFamily_mod_five_table`, `sumFamily_mod_seven_table`, `sumFamily_small_prime_admissible`, `sumFamilyProductPoly_natDegree_le_nine`, `sumFamilyProductPoly_ne_zero_of_prime`, `sumFamily_large_prime_admissible`, `sumFamily_prime_admissible` | VERIFIED | `FactorSumAdmissibility`; 小素数有限表 + 域上非零多项式根数界；精确提交 `900e206d...` 完整 CI 成功 |
| 4.2 | 五项不可约：两二次判别式 `30124,25665` 非平方；三次中心模 19 无根 | `sumFamilyQ_discriminant`, `sumFamilyR_discriminant`, `sumFamilyQ_discriminant_not_square_mod_seven`, `sumFamilyR_discriminant_not_square_mod_seven`, `sumFamilyCenter_scaled_no_root_mod_nineteen`, `sumFamilyPolyU_irreducible_rat`, `sumFamilyPolyV_irreducible_rat`, `sumFamilyPolyQ_irreducible_rat`, `sumFamilyPolyR_irreducible_rat`, `sumFamilyPolyCenter_irreducible_rat`, `sumFamily_five_irreducible_rat` | VERIFIED | `FactorSumIrreducible`; 二次项用判别式非平方，三次中心用模 19 无根；一次项按次数 1 不可约 |
| 4.3 | `P(t)` 严格增长 | `sumFamilyCenter_strictMono` | VERIFIED | 自然参数 |
| 4.4 | Schinzel H 作为显式命题前提，推出本族无穷参数 | `SumFamilySchinzelH`, `sumFamily_infinite_of_schinzelH`, `sumFamily_level_nine_infinite_of_schinzelH` | VERIFIED | `FactorSumSchinzel`; H 仅作为定理参数，不是公理；不可约性与局部相容性由内核定理提供 |
| 4.5 | 经典 Nelson–Penney–Pomerance 族加入中心素性后的模 3 障碍 | `nppFamily_mod_three_obstruction`, `nppFamily_three_dvd_center_of_linear_primes`, `nppFamily_no_prime_center` | VERIFIED | 纯模 3 论证；不把经典四素数构造错误提升为五素数族 |
| 5.1 | Pomerance Ruth–Aaron 计数上界 ⇒ 本问题计数上界 | `sumBalancedPrime_half_mem`, `sumBalancedPrime_half_injOn`, `sumBalancedPrimeCount_le_ruthAaronCount`, `sumBalancedPrimeCount_le_of_ruthAaronBound` | VERIFIED | `FactorSumAnalyticTransfer`; `p ↦ (p-1)/2` 的注入与计数传递为内核证明；外部解析上界保持显式前提 |
| 5.2 | 计数上界 ⇒ 相对素数密度趋零、倒数和收敛 | `sumBalancedPrime_relativeDensity_zero_of_majorant`, `sumBalancedPrime_relativeDensity_zero_of_ruthAaronBound`, `sumBalancedPrime_reciprocal_le_ruthAaron`, `summable_sumBalancedPrime_reciprocals_of_ruthAaron` | VERIFIED | `FactorSumAnalyticTransfer`; 密度极限/RA 倒数和可和性作为显式外部解析输入，传递链本身由 Lean 内核证明 |
| 6.1 | `S(n)≡Ω(n)-v₂(n) (mod 2)` | `primeFactorSum_parity`（等价写成 `S+v₂≡Ω`） | VERIFIED | `FactorSumArithmetic` |
| 6.2 | S 平衡 ⇒ Ω 差与 `v₂` 差同奇偶 | `sumBalanced_count_valuation_parity` | VERIFIED | 有符号差在 `ℤ` |
| 6.3 | 双平衡 ⇒ `p≡1,7 (mod 8)` | `doubleBalanced_mod_eight` | VERIFIED | 必要条件 |
| 6.4 | 双平衡时高 `v₂` 为奇数且 ≥3；共同 S 值 `≡k-1 (mod2)` | `doubleBalanced_two_adic_profile`, `doubleBalanced_common_sum_parity` | VERIFIED | `FactorSumParity` |
| 7.1 | 任意 S 平衡素数且 `TΩ≤8` iff `p∈{11,17,31}` | `sumBalanced_low_count_bound`, `small_sum_balanced_low_count`, `sumBalanced_total_le_eight_iff` | VERIFIED | 先无限范围排除至 `<2000`，再内核证书；不是扫描替代证明 |
| 7.2 | `(2,3),(2,4),(3,3)` 三种半邻数形状及合数中心例外路径 | `sumPair_two_three_bound`, `sumPair_two_four_bound`, `sumPair_three_three_impossible` | VERIFIED | 155、1897 的合数中心由内核证书路径排除 |
| 7.3 | 三例之外 `TΩ≥9` | `sumBalanced_total_ge_nine`, `infinite_sumBalanced_level_ge_nine` | VERIFIED | 完整分类推论 |
| 7.4 | 双平衡共同级数 `k≥5` | `doubleBalanced_level_ge_five` | VERIFIED | 独立结构证明 + 低计数分类均相容 |
| 8.1 | 五级实例 `870404071`，两边分解、共同 S=20936、中心及因子素性 | `doubleBalanced_870404071`, `doubleBalanced_870404071_profile` | VERIFIED | Lean 内核可检查素性；profile 精确给出两侧 S=20936 与 Ω=5 |
| 8.2 | 另一个五级实例 `748465063` | `doubleBalanced_748465063` | VERIFIED | 不宣称数值最小 |
| 8.3 | 可达最小共同级数恰为 5 | `doubleBalanced_minimum_level` | VERIFIED | 存在性 + 下界 |
| 8.4 | 原五项族 `t=5,41529,48465` 的三个中心与第三轮其他回归证书 | `sumFamily_prime_values_five`, `sumFamily_prime_values_41529`, `sumFamily_prime_values_48465`, `sumBalanced_3615811`, `sumBalanced_1676030389155588931`, `sumBalanced_2663854240184425411` | VERIFIED | `FactorSumLucasCertificates` + `FactorSumExamples`; 大整数使用内核可检查 Lucas 证书，不依赖 Python 素性断言 |
| 9.1 | 五级完整形状 `{p-1,p+1}={6bcd,8rs}` 与 `r+s=b+c+d-1` | `HasDoubleFiveShape`, `doubleBalanced_five_has_shape`, `doubleBalanced_five_shape_iff` | VERIFIED | 重复素因子允许 |
| 9.2 | 邻接绝对值式 `|4rs-3bcd|=1` | `doubleBalanced_five_signed_gap`, `doubleBalanced_five_gap_natAbs` | VERIFIED | 同时提供 ±1 有向式和 `Int.natAbs` 形式 |
| 9.3 | 必要模 48 余数 7/41 | `doubleBalanced_five_mod_forty_eight` | VERIFIED | 必要非充分 |
| 9.4 | 两个五级双平衡不能互为孪生；双平衡孪生共同级数 ≥6 | `doubleBalanced_five_not_twins`, `doubleBalanced_twins_level_ge_six` | VERIFIED | 不宣称双平衡孪生存在 |
| 9.5 | 因数对方程及恢复 `K=3bc,L=b+c-1` | `doubleFactorPair_identity`, `doubleFactorPair_iff`, `doubleFactorPair_recover`, `doubleBalanced_five_of_factor_pair_pos`, `doubleBalanced_five_of_factor_pair_neg` | VERIFIED | `x,y` 允许负整数；恢复的素性、正性和中心素性保持为显式前提 |
| 10.1 | “任何无限固定总计数层都 ≥9” | `infinite_sumBalanced_level_ge_nine` | VERIFIED | 无条件有限分类推论 |
| 10.2 | “若五项族参数无限，则存在无限多个 `TΩ=9` S 平衡素数” | `infinite_sumFamily_implies_level_nine` | VERIFIED | 输入显式为参数集合无限 |
| 10.3 | Schinzel H 下最小可无穷出现固定总计数恰为 9 | `sumBalanced_minimum_infinite_level_of_schinzelH` | VERIFIED | `SumFamilySchinzelH` 为显式条件；结合低总计数分类与 `TΩ=9` 参数族，不把 H 当成无条件定理 |

## 当前覆盖

固定清单共 **38** 条：FΣ 源码基线 `e95b7789...` 已达到 **38/38 VERIFIED**。解析数论相关条目只形式化“以外部输入为前提的传递定理”，没有把 Schinzel H 或 Pomerance 解析估计加入为公理。当前剩余工作仅是与最新 `master` 集成、PR 合并及最终 `master` 精确提交的 CI 验收。

## 当前停止条件

只有当上表所有 **有效** 条目均转为 VERIFIED，所有 `EXTERNAL-INPUT` 条目已有清楚的“以外部输入为前提”的 Lean 传递定理，最终 PR 合入 `master`，并且最终 `master` 精确提交的 Lean CI 成功，才满足任务停止条件。

若后续发现某条数学陈述错误，应在本表保留原条目并改为 **REFUTED**，附反例和替代陈述；不得静默弱化。

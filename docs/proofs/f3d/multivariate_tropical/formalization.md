# F3D-MULTI：形式化映射与阻塞依赖

数学状态分项：MULTI-1/2、MULTI-3 构造方向、有限热带 Lipschitz 界与固定幅度开关保留 PAPER-AUDITED；MULTI-3 必要性和依赖它的 MULTI-4 全体可实现函数路线为 RESEARCH（审计缺口）。Lean 状态：NOT-STARTED。

[定理](theorem.md) · [完整证明](proof.md) · [PDF](paper.pdf) · [引理 DAG](scaffolding.md)

## 1. 推荐模块

- OmegaBalance/F3DMultivariateLocal.lean
- OmegaBalance/F3DMultivariateTropical.lean
- OmegaBalance/F3DInterpolation.lean

## 2. 目标接口

| 节点 | 建议 Lean 名称 | 状态 |
|---|---|---|
| MULTI-L2 | f3D_positive_indicator_quadratic | 未实现 |
| MULTI-L3 | padicVal_mu_eq_min | 未实现 |
| MULTI-L4 | padicVal_mu_max | 未实现 |
| MULTI-L5 | weighted_power_sum_val | 未实现 |
| MULTI-L6 | weighted_power_sum_min_and_argmin | 未实现 |
| MULTI-L7 | integerTropical_normal_form | 未实现 |
| MULTI-L8/L9 | f3D_realize_integerTropical | 未实现 |
| MULTI-L10 | f3D_integer_grid_realization | 未实现 |
| MULTI-L11 | lagrange_unit_grid_valuation_bound | 未实现 |
| MULTI-L12 | polyValuation_piecewiseAffine_on_grid | 未实现；仅保留有限分区范围，禁止附加错误的热带等价断言 |
| MULTI-L13 | f3D_grid_minimum_recovers_output | 未实现；恢复恒等式本身不依赖 L12 |
| MULTI-L14 | f3D_multivariate_realizable_iff_tropical | RESEARCH 阻塞；必要性未修复，不可据原证明实施 |
| MULTI-L15 | integerTropical_lipschitz | 未实现；只对有限整数热带表达式 |
| MULTI-L16 | f3D_unbounded_switch_not_realizable | RESEARCH 阻塞；非热带性不足以证明不可实现 |
| MULTI-L17 | f3D_bounded_switch_realizable | 未实现 |
| MULTI-L18 | padicVal_mu_prime_eq_min | 未实现 |

## 3. 推荐形式化顺序

第一阶段：Theta、mu、H_k 唯一最低项、min/max 与第一极小位置。这些可直接复用 padicValRat 与 ring 运算。

第二阶段：定义有限整数热带表达式语法，证明闭包、Lipschitz 以及“两个 tropical polynomial 之差”的正规形。

第三阶段的原必要性路线暂停：实际输入网格、Lagrange 插值界与网格最小值恢复恒等式可独立考虑，但固定网格赋值的“有限分区即热带”已被否定。需先提供并审计必要性的新证明；不得把待证分类作为假设完成同名目标。本次不扩大广义理论的任务范围。

## 4. 语义约束

1. 多输入全域实现必须保证输出对所有合法输入仍在定义域。
2. 输入数 m 固定；第一极小位置构造的输出范围因此有限。
3. 分类只在整数格点 Z^m 上断言相等，不要求对应实分段线性函数在 R^m 上唯一。
4. 中间可使用有理函数，但最终 realization 必须回到整数多项式对。
5. 必要性必须使用实际整数输入，不能只在抽象 valuation vector 上推断。
6. 插值界的次数参数可取每变量次数上界；总次数上界也可安全替代。
7. 一般素数 p 版本应与 p=3 主项目接口分开，避免把模 3 特性错误普遍化。

## 5. 外部依赖

没有 Green–Tao 型外部阻塞。构造与基础引理主要依赖 padicValRat 的乘法/加法/幂规则、多项式 Lagrange 插值和有限 min/max 代数。必要性另有内部数学阻塞 `F3D-CORR-MULTI-L12`，不能称为只待工程实现。

## 6. 验证登记

| 项目 | 状态 |
|---|---|
| 书面证明 | 构造等分项保留；必要性路线存在缺口 |
| 书面审计 | 分项状态见 theorem.md；整体 PAPER-AUDITED 已撤回 |
| PDF | workflow 生成 |
| 新增 Lean 声明 | 0 |
| Lean kernel 验证 | 无 |
| 主结果状态 | Lean NOT-STARTED；分类必要性数学状态 RESEARCH |

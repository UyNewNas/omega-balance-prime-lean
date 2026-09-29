# F3-HI：形式化映射与阻塞依赖

数学状态：`PAPER-AUDITED`。Lean 状态：`NOT-STARTED`。

[定理](theorem.md) · [证明](proof.md) · [引理 DAG](scaffolding.md)

## 1. 建议模块拆分

建议分三层：

1. `OmegaBalance/F3HigherInteractionsLocal.lean`
   - 只处理局部确定性公式、余因子 (G_n(d))、简单根提升和有限模计数。
2. `OmegaBalance/F3HigherInteractionsPattern.lean`
   - 处理有限剩余模式、CRT 偏移构造和单项式模式稳定性。
3. `OmegaBalance/F3HigherInteractionsPrime.lean`
   - 只在找到真实可用的外部素数线性形式接口后接入全局无穷性与渐近计数。

不要为了“完成主定理”而把 Green–Tao 计数写成自定义公理。

## 2. 目标接口

| 书面节点 | 建议 Lean 名称 | 模块 | 状态 | 依赖 |
|---|---|---|---|---|
| HI-L1 | `f3_eq_pos_iff_v3_add_one` 或复用现有接口 | Local | 待检索 | 现有 `f3`、`v3` |
| HI-L2 | `f3_three_point_shape` | Local | 未实现 | `Nat.ModEq`、赋值同余稳定 |
| HI-L3 | `f3_pair_products_shape` | Local | 未实现 | 乘积模 (3^{k+1}) |
| HI-L4 | `f3_triple_product_factor` | Local | 未实现 | 环算术 |
| HI-L5 | `f3_G_mod_three`、`f3_G_deriv_mod_three` | Local | 未实现 | `ZMod 3` |
| HI-L6 | `f3_G_unique_root_mod_pow` | Local | 未实现 | Hensel 型有限归纳 |
| HI-L6-count | `f3_G_root_count_units` | Local | 未实现 | `Finset` / `ZMod` 单位计数 |
| HI-L12 | `f3_pattern_offsets_exists` | Pattern | 未实现 | CRT |
| 单项式稳定 | `f3_monomial_pattern_stable_mod_pow` | Pattern | 未实现 | 赋值同余稳定 |
| HI-L7/8 | `f3_hi_prime_system_local_admissible` | Prime | 未实现 | 外部系统复杂度定义 |
| EXT-GT2 | 名称待真实库检索 | 外部 | `BLOCKED-EXTERNAL` | Green–Tao 复杂度至多 2 |
| EXT-GTF | 名称待真实库检索 | 外部 | `BLOCKED-EXTERNAL` | 一般有限复杂度 |
| F3-HI-1 | `f3_higher_interactions_distribution` | Prime | 阻塞 | 需要渐近计数框架 |
| F3-HI-2 | `f3_second_order_not_determine_triple` | Prime | 阻塞 | F3-HI-1 |
| F3-HI-3 | `f3_finite_pattern_prime_realization` | Prime | 阻塞 | EXT-GTF |

## 3. 可先形式化的无外部深定理部分

以下内容完全不依赖 Green–Tao，可优先进入 Lean：

- 六个低阶值锁定；
- 三因子精确因子分解；
- (G_n(d)) 模 3 唯一简单根；
- 模 (3^T) 根数与精确层比例；
- 固定有限模数下的单项式 (F_3) 模式稳定性；
- CRT 偏移构造本身；
- 有限素数 (ell) 的局部可解性陈述。

这些结果即使先形式化，也只能报告为“局部/有限层 Lean 已证”，不能把主无穷性定理标成 `LEAN-PROVED`。

## 4. 语义约束

1. 所有有符号 (F_3) 差分使用 (mathbb Z)，先 cast 后相减。
2. 不改变仓库当前 (v_3(0)) 的全函数约定；通过 (n>1,d>0) 排除纸面证明中的零输入。
3. 主结果的 (d) 必须是变量且最终要求为素数；不能错误固定为常量。
4. (kge1) 是核心前提；(k=0) 不属于本定理。
5. (Rge k+1)；不存在 (Rle k) 的目标分支。
6. F3-HI-3 的一般模式以“有限模稳定”表述，不引入未经定义的 3-adic (F_3)。

## 5. 外部依赖策略

在继续全局形式化前，先检索现有 Lean 数论库是否已经有：

- 有限复杂度仿射线性形式系统；
- von Mangoldt/素数模式渐近；
- Green–Tao 或同等强度的可复用形式化接口。

若不存在，主全局定理应保持 paper 状态。允许证明“若外部计数定理成立，则 F3-HI-1 成立”的桥接 theorem，但必须在名称和 README 中明确是条件命题，不能冒充无条件形式化。

## 6. 验证登记

| 项目 | 当前状态 |
|---|---|
| 完整书面证明 | 已整理 |
| 书面审计 | 已完成 |
| 新增 Lean 声明 | 0 |
| Lean kernel 验证 | 不适用：本提交无 Lean 代码 |
| 外部深定理形式化接口 | 未确认 |
| 主结果 Lean 状态 | `NOT-STARTED` / `BLOCKED-EXTERNAL` |

未来新增任何 Lean 声明后，必须登记 `scripts/Audit.lean` 并在同一精确 head 上完成仓库要求的完整验证。

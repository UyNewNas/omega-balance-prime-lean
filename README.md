# Ω 与质因数和平衡素数：定理与猜想地图

本仓库形式化 Ω 计重个数平衡、质因数计重求和平衡、两者的双平衡，以及素数邻数的三进赋值差分。已形式化定理与尚未证明的猜想分区列出。

## 研究成果生命周期与提交规范

本仓库同时保存数学探索、书面证明与 Lean 形式化结果。不同成熟度的内容必须分层记录，避免把计算证据、纸面证明和内核证明混为一谈。

### 结果状态

建议所有重要命题使用稳定编号（如 `F3-COR-1`、`F3-PAT-1`、`OBG-1`），并在不同阶段沿用同一编号。状态按下列生命周期推进：

```text
CONJECTURE
  ↓
EXPERIMENTAL / RESEARCH
  ↓
PAPER-PROVED
  ↓
PAPER-AUDITED
  ↓
FORMALIZATION-READY
  ↓
LEAN-IN-PROGRESS
  ↓
LEAN-PROVED
```

另设 `REFUTED`，用于已发现反例或证明为假的命题。

各状态含义：

- **CONJECTURE**：精确命题已经提出，但尚无证明。
- **EXPERIMENTAL / RESEARCH**：有计算、结构观察、启发式推导或尚未封闭的证明尝试。
- **PAPER-PROVED**：已有完整的人类可读书面证明，但尚未经过独立审计。
- **PAPER-AUDITED**：书面证明已逐步检查，关键依赖、量词、边界条件与外部定理使用均已确认；这已经是数学意义上的证明，但**不等于 Lean 内核证明**。
- **FORMALIZATION-READY**：书面证明已经拆成适合形式化的引理 DAG，并明确外部依赖、目标 Lean 接口和阻塞项。
- **LEAN-IN-PROGRESS**：部分引理已进入 Lean，但主结论尚未通过完整门禁。
- **LEAN-PROVED**：目标结论已经由 Lean kernel 检查，并且精确提交通过本仓库要求的构建、回归、公理与审计覆盖门禁。
- **REFUTED**：命题已被反例或证明否定；保留记录以防重复探索。

**核心原则：`PAPER-AUDITED` 不是 `CONJECTURE`，也不是 `LEAN-PROVED`。** 已审计书面证明可以直接提交到主仓库，不需要等待 Lean 形式化完成；同时不得在 README、PR 或提交信息中把纸面证明描述成“已形式化”。

### 内容放置

当前仓库按以下职责维护；已有历史目录无需为了形式统一而一次性大规模搬迁。

| 内容类型 | 推荐位置 | 要求 |
|---|---|---|
| 猜想与精确命题 | `docs/conjectures/` | 写清量词、例外、当前证据和已知反例 |
| 探索笔记、round 记录 | `docs/*_research/`，当前 F₃ 使用 `docs/f3_balance_research/` | 允许未完成推导、实验、失败路线和开放问题 |
| 已证明但暂未形式化的书面证明 | `docs/proofs/<topic>/<result>/` | 必须明确 paper 状态，不得冒充 Lean 定理 |
| 形式化任务、依赖和进度账本 | `docs/*formalization*.md`；后续新主题可用 `docs/formalization/` | 记录依赖 DAG、目标接口、阻塞项与精确验证状态 |
| Lean 定义与证明 | `OmegaBalance/*.lean` | 遵守 `AGENTS.md`，禁止占位证明和自定义数学公理 |
| 有限计算、实验输出、审计报告 | `reports/`、`data/` | 明确说明有限验证不能替代无限命题证明 |

### 已审计书面证明的提交结构

对于一个已经得到可靠书面证明、但尚未完成 Lean 形式化的重要结果，推荐直接建立：

```text
docs/proofs/<topic>/<result>/
├── theorem.md
├── proof.md
├── scaffolding.md
├── formalization.md
├── paper.pdf
└── paper.tex        # 推荐；使用定制 LaTeX 排版时保留可复现源
```

核心五件套为四个 Markdown + `paper.pdf`；若使用定制 LaTeX 排版，额外保留 `paper.tex` 作为可复现源：

- `theorem.md`：只保存最终、稳定、精确的定理陈述，标明结果 ID、状态、前提、外部依赖和边界情况。
- `proof.md`：保存适合数学阅读的干净书面证明。不要混入大量探索历史或 Lean 实现细节。
- `scaffolding.md`：把证明拆成引理、依赖 DAG 和可逐个核验的局部步骤；这是书面证明与 Lean 之间的脚手架。
- `formalization.md`：记录每个书面引理对应的目标 Lean 名称、目标模块、完成状态、阻塞依赖和最终核验提交。
- `paper.pdf`：面向阅读、归档和引用的稳定排版版本。内容应与当前已审计的定理和证明一致；PDF 是书面证明的呈现层，不代表 Lean kernel 验证。
- `paper.tex`：推荐保留的 PDF 排版源。仓库工作流在它变化时自动构建 `paper.pdf`；简单结果也可采用其他可复现生成方式，但最终 PDF 仍是必需交付物。

简单结果不必机械拆成四个文件；但凡证明较长、依赖外部深定理、或预计需要多轮形式化，优先采用上述结构。

### 书面证明准入要求

标记为 `PAPER-AUDITED` 并提交前，至少确认：

1. 定理陈述已经固定，量词、定义域、非零/正性条件、边界例外均明确。
2. 证明中的每一步都可定位到已证明引理、明确计算或可靠外部定理。
3. 外部定理写明准确版本和实际使用的结论，不能只写“由某著名定理可得”。
4. 计算实验只作为 sanity check 或证据，不承担无限范围证明责任。
5. 尚未形式化的部分明确写为 paper proof；不得使用“Lean verified”“kernel checked”等措辞。
6. PDF 已从当前稳定书面证明生成，并完成至少一次渲染检查，确认无文字裁切、公式溢出、缺字或乱码；PDF 中应标明结果 ID、paper 状态及“尚未形式化”边界。
7. 若审计发现缺口，状态应退回 `PAPER-PROVED`、`RESEARCH` 或 `CONJECTURE`，而不是保留错误的高状态。

### Lean 结果准入要求

只有在目标定理真正进入 Lean 且通过精确 head 的完整验证后，才能标记 `LEAN-PROVED`。继续遵守 `AGENTS.md` 中的规则，尤其是：

- 禁止 `sorry` / `admit`、自定义数学公理、unsafe/native proof escape；
- 每条项目 theorem/lemma 必须登记到 `scripts/Audit.lean`；
- 有符号统计量必须按既定整数语义处理；
- 有限计算、源码检查和纸面推导都不能替代 Lean kernel 检查；
- 声称“验证通过”前运行 `python3 scripts/verify.py`，或确认同一精确 Git head 的 CI 已成功。

### 提交与 PR 命名

提交信息应同时表达“内容类型”和“成熟度”，避免只写含糊的 `update notes`。

推荐前缀：

```text
conjecture: ...
research: ...
proof: ...
docs: ...
formalize: ...
feat: ...
fix: ...
refactor: ...
audit: ...
```

示例：

```text
proof: add audited paper proof of F3 four-prime construction
research: record F3 affine-kernel round 8
formalize: add residue lemmas for F3-PAT-1
feat: formalize F3-PAT-1 four-prime construction
audit: register F3-PAT-1 declarations
```

其中：

- 纯书面数学证明优先用 `proof:`；
- 探索过程用 `research:`；
- 正在搭 Lean 脚手架但主结论未完成时用 `formalize:`；
- 已形成稳定 Lean 功能或主定理时可用 `feat:`；
- 不要在未通过完整 Lean 门禁前使用会暗示“形式化已完成”的标题。

对于较大的结果，PR 描述至少应列出：结果 ID、当前状态、数学结论、外部依赖、是否包含 Lean 证明、精确验证状态、PDF 生成/渲染检查状态，以及明确的“本 PR 不声称什么”。

### 仓库维护原则

本仓库的四层知识应长期同时保留：

> **探索记录发现过程；书面证明固化数学知识；脚手架暴露证明结构；Lean 固化机器核验。**

不要为了追求目录整齐而删除有价值的历史探索，也不要因为已有 Lean 证明就自动删除高质量书面证明。两者服务于不同读者，也承担不同的审计职责。


## 记号

$\Omega(n)$ 表示质因数总个数，**按重数计**；$S(n)$ 表示质因数本身计重求和；$v_q(n)$ 表示素因子 $q$ 的指数。对 $n>1$，记

$$
\begin{aligned}
F_\Omega(n)&=\Omega(n+1)-\Omega(n-1),&T_\Omega(n)&=\Omega(n-1)+\Omega(n+1),\\
F_\Sigma(n)&=S(n+1)-S(n-1),&F_3(n)&=v_3(n+1)-v_3(n-1).
\end{aligned}
$$

| Lean 定义 | 数学含义 |
|---|---|
| `bigOmega` | $\Omega(n)$，质因数计重**个数** |
| `omegaDiff`、`omegaSum` | $F_\Omega(n)$、$T_\Omega(n)$；`omegaSum` 不是质因数求和 |
| `primeFactorSum`、`primeFactorSumDiff` | $S(n)$、$F_\Sigma(n)$ |
| `primeFactorDefect` | $D(n)=n-S(n)$ |
| `f3` | $F_3(n)$ |
| `IsOmegaBalancedPrime p` | $p$ 为素数且左右 Ω 相等 |
| `IsPrimeFactorSumBalancedPrime p` | $p$ 为素数且左右 S 相等 |
| `IsDoubleBalancedPrime p k` | $p$ 为素数、左右 S 相等，且左右 Ω 均为 $k$ |

所有差分在整数中计算。下表定理位于 `OmegaBalance` 命名空间，链接指向形式化源码。

## Ω 与 F₃ 主定理地图

| 主定理 | 前提 | 数学结论 | Lean 定理 |
|---|---|---|---|
| **孪生素数的精确反号** | $p,p+2$ 均为素数，$p>3$ | $F_3(p+2)=-F_3(p)$，且两者均非零 | [`f3_twin`](OmegaBalance/F3.lean) |
| **精确反号的同余推广** | $n>1$，$n\equiv2\pmod3$，不要求素数性 | $F_3(n+2)=-F_3(n)$，且两者均非零 | [`f3_opposite_of_mod_three`](OmegaBalance/F3.lean) |
| **Ω 平衡的零点刻画** | $p\ge2$ | $p$ 为 Ω 平衡素数，当且仅当 $p$ 为素数且 $F_\Omega(p)=0$ | [`isOmegaBalancedPrime_iff`](OmegaBalance/Basic.lean) |
| **奇数邻项约去公共因子 2** | $n>1$ 为奇数 | $F_\Omega(n)=\Omega((n+1)/2)-\Omega((n-1)/2)$；平衡等价于两个相邻半邻数的 Ω 相等 | [`omegaDiff_eq_half_diff`](OmegaBalance/Basic.lean)、[`isOmegaBalanced_iff_half`](OmegaBalance/Basic.lean) |
| **邻项总计数的乘积公式** | $n>1$ | $T_\Omega(n)=\Omega((n-1)(n+1))=\Omega(n^2-1)$ | [`omegaSum_eq_bigOmega_product`](OmegaBalance/Basic.lean)、[`omegaSum_eq_bigOmega_sq_sub_one`](OmegaBalance/Basic.lean) |

## 质因数和与双平衡主定理地图

| 主定理 | 前提 | 数学结论 | Lean 定理 |
|---|---|---|---|
| **五素数参数族** | `SumFamilyPrimeValues t`：指定的两个一次式、两个二次式和中心三次式均为素数 | 中心 $P(t)$ 为 S 平衡素数；左右 Ω 分别为 5、4，总计数 9，Ω 差为 −1 | [`sumFamily_five_primes`、`sumFamily_left_profile`、`sumFamily_right_profile`](OmegaBalance/FactorSumFamily.lean) |
| **低总计数完整分类** | 任意自然数 $p$ | $p$ 为 S 平衡素数且 $T_\Omega(p)\le8$，当且仅当 $p\in\{11,17,31\}$ | [`sumBalanced_total_le_eight_iff`](OmegaBalance/FactorSumLowCount.lean) |
| **双平衡的最小可达级数** | 两邻数同时求和平衡、且 Ω 均为 $k$ | 必有 $k\ge5$；确实存在 $k=5$ 的素数 | [`doubleBalanced_level_ge_five`](OmegaBalance/FactorSumStructure.lean)、[`doubleBalanced_minimum_level`](OmegaBalance/FactorSumExamples.lean) |
| **五级双平衡完整形状** | $p$ 为素数 | 五级双平衡等价于 $\{p-1,p+1\}=\{6bcd,8rs\}$，其中 $b,c,d,r,s$ 为奇素数且 $r+s+1=b+c+d$；同侧可重复因子 | [`doubleBalanced_five_shape_iff`](OmegaBalance/FactorSumFive.lean) |
| **双平衡孪生限制** | $p,p+2$ 分别为 $k,j$ 级双平衡素数 | $k=j\ge6$；五级双平衡素数不能成孪生对 | [`doubleBalanced_twins_level_ge_six`、`doubleBalanced_five_not_twins`](OmegaBalance/FactorSumFive.lean) |

五参数族的具体表达式、接口和证明依赖见[求和平衡形式化地图](docs/sum_balance/formalization.md)。上述构造是带显式素性前提的蕴含，不声称已经证明了无穷多个参数同时为素数。

## 质因数和的运算与结构推论

| 结论 | 前提与数学内容 | Lean 定理 |
|---|---|---|
| 完全可加性与素数幂 | $a,b>0$ 时 $S(ab)=S(a)+S(b)$；素数 $q$ 满足 $S(q^k)=kq$ | [`primeFactorSum_mul`、`primeFactorSum_prime_pow`](OmegaBalance/FactorSum.lean) |
| 大小界与素数刻画 | $S(n)\le n$；$n>0$ 时，等号当且仅当 $n$ 为素数或 $n=4$ | [`primeFactorSum_le`、`primeFactorSum_eq_self_iff`](OmegaBalance/FactorSumArithmetic.lean) |
| 零点与半邻数 | $F_\Sigma(n)=0$ 等价于左右 S 平衡；奇数 $n>1$ 可同时约去邻数中的一个因子 2 | [`primeFactorSumDiff_eq_zero_iff`、`primeFactorSumBalanced_iff_half`](OmegaBalance/FactorSum.lean) |
| 一般余因子构造 | $A,B>0$，$q,r$ 素数，$Br=Aq+1$ 且 $S(A)+q=S(B)+r$；若 $2Aq+1$ 为素数，则它求和平衡 | [`primeFactorSum_cofactor_construction`](OmegaBalance/FactorSum.lean) |
| 精确缺陷公式 | 参数族中只要求 U、V 为素数；Q、R 允许合数 | $F_\Sigma(P)=D(Q)-D(R)$；平衡当且仅当两个缺陷相等 | [`sumFamily_defect_identity`、`sumFamily_balanced_iff_defect`](OmegaBalance/FactorSumFamily.lean) |
| 奇偶耦合 | $S(n)+v_2(n)\equiv\Omega(n)\pmod2$；S 平衡时 $F_\Omega(n)\equiv v_2(n+1)-v_2(n-1)\pmod2$ | [`primeFactorSum_parity`、`sumBalanced_count_valuation_parity`](OmegaBalance/FactorSumArithmetic.lean) |
| 双平衡的模 8 限制 | 任意级数双平衡素数满足 $p\equiv1$ 或 $7\pmod8$ | [`doubleBalanced_mod_eight`](OmegaBalance/FactorSumArithmetic.lean) |
| 五级的模 48 限制 | 五级双平衡素数满足 $p\equiv7$ 或 $41\pmod{48}$ | [`doubleBalanced_five_mod_forty_eight`](OmegaBalance/FactorSumFive.lean) |
| 其余 S 平衡素数的总计数 | 排除 $11,17,31$ 后，必有 $T_\Omega(p)\ge9$ | [`sumBalanced_total_ge_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 固定总计数的无穷性下界 | **若**某个总计数 $k$ 层有无穷多个 S 平衡素数，则 $k\ge9$ | [`infinite_sumBalanced_level_ge_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 参数无穷性的传递 | **若**五项素数参数集合无限，则总计数 9 的 S 平衡素数集合无限；定理不证明其输入前提 | [`infinite_sumFamily_implies_level_nine`](OmegaBalance/FactorSumLowCount.lean) |
| 五级因数对恒等式 | 整数 $d=r+s-L$ 时，$4rs-Kd=e$ 等价于 $(4r-K)(4s-K)=K(K-4L)+4e$ | [`doubleFactorPair_iff`](OmegaBalance/FactorSumFamily.lean) |

## 孪生素数及三进赋值的推论

下表前五行均假设 $p,p+2$ 为素数且 $p>3$；最后两行只要求 $p>3$ 为素数。

| 推论 | 数学结论 | Lean 定理 |
|---|---|---|
| 共享邻数给出精确幅度 | $F_3(p)=v_3(p+1)>0$，$F_3(p+2)=-v_3(p+1)$ | [`f3_twin_values`](OmegaBalance/F3.lean) |
| 符号方向固定 | $F_3(p)>0$，$F_3(p+2)<0$ | [`f3_twin_signs`](OmegaBalance/F3.lean) |
| 绝对值相等 | $\lvert F_3(p+2)\rvert=\lvert F_3(p)\rvert$ | [`f3_twin_abs_eq`、`f3_twin_natAbs_eq`](OmegaBalance/F3.lean) |
| 乘积严格为负 | $F_3(p)F_3(p+2)<0$ | [`f3_twin_mul_neg`](OmegaBalance/F3.lean) |
| 模六结构 | $p\equiv5\pmod6$，$6\mid p+1$；存在 $k>0$ 使 $p=6k-1$、$p+2=6k+1$ | [`twin_mod_six`、`six_dvd_twin_center`、`twin_six_mul_form`](OmegaBalance/F3.lean) |
| 大于三的素数均非零 | $F_3(p)\ne0$ | [`f3_ne_zero_of_prime`](OmegaBalance/F3.lean) |
| 符号由模三余数刻画 | $F_3(p)>0\iff p\equiv2\pmod3$；$F_3(p)<0\iff p\equiv1\pmod3$ | [`f3_pos_iff_mod_three`、`f3_neg_iff_mod_three`](OmegaBalance/F3.lean) |

## Ω 平衡与赋值的相关结论

| 结论 | 前提与数学内容 | Lean 定理 |
|---|---|---|
| 一般中心的零点判据 | $n>1$ 时，$F_\Omega(n)=0\iff\Omega(n-1)=\Omega(n+1)$，不要求素数性 | [`omegaDiff_eq_zero_iff`](OmegaBalance/Basic.lean) |
| 素数邻项约去因子 2 | 素数 $p>2$ 满足 $F_\Omega(p)=\Omega((p+1)/2)-\Omega((p-1)/2)$ | [`omegaDiff_prime_eq_half_diff`](OmegaBalance/Basic.lean) |
| 和差恢复左右计数 | $T_\Omega(n)+F_\Omega(n)=2\Omega(n+1)$，$T_\Omega(n)-F_\Omega(n)=2\Omega(n-1)$；等式在整数中理解 | [`omegaSum_add_omegaDiff`、`omegaSum_sub_omegaDiff`](OmegaBalance/Basic.lean) |
| Ω 的完全可加性与素数幂 | $a,b>0$ 时 $\Omega(ab)=\Omega(a)+\Omega(b)$；素数 $q$ 满足 $\Omega(q^k)=k$ | [`bigOmega_mul`、`bigOmega_prime_pow`](OmegaBalance/Basic.lean) |
| 赋值与整除等价 | 素数 $q$、$n>0$ 满足 $v_q(n)>0\iff q\mid n$ | [`valuation_pos_iff_dvd`](OmegaBalance/Valuation.lean) |
| 赋值的乘法与幂 | 素数 $q$、$a,b>0$ 满足 $v_q(ab)=v_q(a)+v_q(b)$；$v_q(q^k)=k$ | [`valuation_mul`、`valuation_prime_pow`](OmegaBalance/Valuation.lean) |

## F₃ 的整数延拓与运算定理

`f3Int : ℤ → ℤ` 保留原 `f3 : ℕ → ℤ`。以下结果不要求素数性；非零及互素前提见对应源码与 [F₃ 整数延拓说明](docs/f3_extension.md)。

| 内容 | 数学结论与范围 | Lean 接口 |
|---|---|---|
| 整数兼容与奇函数 | $n\ge1$ 时 `f3Int n = f3 n`；所有整数满足 `f3Int (-z) = -f3Int z` | [`f3Int_nat`、`f3Int_neg`](OmegaBalance/F3Extension.lean) |
| 零点分类 | $n>1$ 时，$F_3(n)=0\iff3\mid n$ | [`f3_eq_zero_iff_three_dvd`](OmegaBalance/F3Extension.lean) |
| 平方 | $n>1,3\nmid n$ 时，$F_3(n^2)=-\lvert F_3(n)\rvert$ | [`f3_sq`](OmegaBalance/F3Extension.lean) |
| 立方与迭代立方 | $n>1,3\nmid n$ 时，符号不变，每次立方使层级增加 1 | [`f3_cube`](OmegaBalance/F3Extension.lean)、[`f3_iterated_cube_pos`、`f3_iterated_cube_neg`](OmegaBalance/F3Arithmetic.lean) |
| 乘法 | $m,n>1,3\nmid mn$ 时，层级至少为两个输入层级的较小值；异层时恰取较小者，符号有精确规则 | [`f3_mul_depth`、`f3Side_mul`](OmegaBalance/F3Arithmetic.lean) |
| 修正间距 | 输入层级不同时，修正间距的赋值恰为较小层级；使用整数差 | [`f3_adjusted_gap_valuation`](OmegaBalance/F3Arithmetic.lean) |
| 固定和反射 | $a,b>1,3\nmid a,3\mid a+b$ 且 $\lvert F_3(a)\rvert<v_3(a+b)$ 时，$F_3(b)=-F_3(a)$ | [`f3_reflection`](OmegaBalance/F3Arithmetic.lean) |

## F₃ 深层推论的形式化接口

以下入口及精确前提见 [F₃ 深层形式化地图](docs/f3_deeper_formalization.md)。

| 内容 | 主要结论 | Lean 接口 |
|---|---|---|
| 任意正整数幂 | 层级增加 $v_3(e)$，符号由底数余数及指数奇偶决定 | [`f3_pow_depth`、`f3Side_pow`、`f3_pow`](OmegaBalance/F3Powers.lean) |
| 有理延拓与 Cayley 运算 | $\Phi((x y+1)/(x+y))=\Phi(x)+\Phi(y)$；保留零点与极点例外 | [`f3Rat_star`、`f3Rat_star_of_gt_one`](OmegaBalance/F3Rational.lean) |
| Cayley 结合律 | $x,y,z>1$ 时 $x\star y=(xy+1)/(x+y)$ 结合，Cayley 变换将它变为乘法 | [`f3Cayley_star`、`f3Cayley_involution`、`f3Star_assoc`](OmegaBalance/F3Rational.lean) |
| 反号配对的和积关系 | $n-m=2+3^kT$ 时，$v_3(mn-1)$ 与 $v_3(m+n)$ 的较小者由 $v_3(T)$ 决定 | [`f3_opposite_sum_product`、`f3_product_refined_gap`](OmegaBalance/F3SumProduct.lean) |
| 孪生乘积与间距阈值 | 孪生对满足 $F_3(p(p+2))=2F_3(p)$；推出乘积阈值下的间距二择一 | [`f3_twin_product`、`f3_product_gap_dichotomy`](OmegaBalance/F3SumProduct.lean) |
| 模 $3^k$ 的乘法阶 | 依正负侧得到阶 $3^{\max(k-a,0)}$ 或其两倍；孪生对的阶相差两倍 | [`f3_orderOf`、`f3_twin_orderOf`](OmegaBalance/F3Order.lean) |
| 同层进位判据 | 首单位数字和模 3 为零，当且仅当乘积层级严格上升 | [`f3_same_level_cancellation`、`f3_same_level_rises_iff`](OmegaBalance/F3Coordinates.lean) |
| 原根塔判据 | $F_3(n)=1$ 等价于模 9 的阶为 6，也等价于所有 $3^k$ 上达到最大阶 | [`f3_eq_one_iff_order_nine`、`f3_eq_one_iff_maximal_order_tower`](OmegaBalance/F3Primitive.lean) |
| 有限截断与望远镜求和 | 截断函数以 $3^K$ 为周期，等于截断后的 $F_3$；连续整数求和只剩边界项 | [`f3Trunc_periodic`、`f3Trunc_eq_clipped`、`f3_sum_range`](OmegaBalance/F3Finite.lean) |

## 已形式化的实例与反例

| 实例或反例 | 已证明的结论 | Lean 定理 |
|---|---|---|
| Ω 平衡实例 $p=5$ | $5$ 是 Ω 平衡素数 | [`five_isOmegaBalancedPrime`](OmegaBalance/Examples.lean) |
| 小 S 平衡实例 | $11,17,31$ 均为求和平衡素数 | [`sumBalanced_11`、`sumBalanced_17`、`sumBalanced_31`](OmegaBalance/FactorSumExamples.lean) |
| 参数族实例 | $t=5$ 的五项均为素数，中心 $3615811$ 求和平衡，Ω 总计数 9、差 −1 | [`sumFamily_prime_values_five`、`sumBalanced_3615811`、`sumBalanced_3615811_profile`](OmegaBalance/FactorSumExamples.lean) |
| 五级双平衡实例 | $870404071$、$748465063$ 两个中心及各因子的素性均被证明，左右均为五个因子且总和相等 | [`doubleBalanced_870404071`、`doubleBalanced_748465063`](OmegaBalance/FactorSumExamples.lean) |
| 孪生对 $(17,19)$ | $F_3(17)=2$，$F_3(19)=-2$ | [`twin_seventeen_nineteen_example`](OmegaBalance/Examples.lean) |
| 例外孪生对 $(3,5)$ | $F_3(3)=0$、$F_3(5)=1$；主定理的 $p>3$ 不能删去 | [`exceptional_twin_three`](OmegaBalance/Examples.lean) |
| 反号不是孪生的充分条件 | 素数 $5,13$ 的 F₃ 值是非零相反数，但不是孪生对 | [`opposite_f3_not_sufficient_for_twins`](OmegaBalance/Examples.lean) |
| F₃ 对称性不能移植到 Ω 差分 | 孪生对 $(5,7)$ 满足 $F_\Omega(5)=0$、$F_\Omega(7)=1$ | [`omegaDiff_twin_five_seven`](OmegaBalance/Examples.lean) |
| F₃ 两标量不能确定乘积 | $F_3(5)=F_3(11)=1$，但与 7 相乘后分别得到 −2 与 −1 | [`f3_no_scalar_mul_rule`](OmegaBalance/F3DeeperExamples.lean) |

## 已审计书面证明（尚未形式化）

以下结果状态为 `PAPER-AUDITED`：书面证明及外部定理的适用条件已经复核，主结果尚未写入 Lean。

| 编号 | 数学结论 | 状态与外部依赖 |
|---|---|---|
| [F3-PAT-1](docs/proofs/f3/four_prime_construction/theorem.md) | 无穷多个正整数参数对 $(n,d)$ 使 $n,n+38d,n+92d,n+146d$ 全为素数，单点 $F_3$ 模式为 $(1,-1,-1,-1)$，三个以 $n$ 为中心的乘积模式为 $(3,5,3)$ | `PAPER-AUDITED`；Green–Tao, *Linear equations in primes*, Corollary 1.7 的无条件复杂度至多 2 情形 |
| [F3-HI-1 / F3-HI-2](docs/proofs/f3/higher_interactions/theorem.md) | 固定形状 $(n,n+2\cdot3^{k+1}d,n+6\cdot3^{k+1}d)$ 中，三个单点值全为 $k$、三个两两乘积值全为 $-k$，但三因子值具有显式几何深度分布并可取任意 $R\ge k+1$；因此全部二阶数据不能控制三阶输出 | `PAPER-AUDITED`；主计数使用 Green–Tao 复杂度至多 2 的无条件素数线性形式定理 |
| [F3-HI-3](docs/proofs/f3/higher_interactions/theorem.md#4-定理-f3-hi-3有限剩余模式的素数伸缩实现) | 任意有限的三进单位剩余模式可嵌入某个固定二参数伸缩族，并由无穷多组素数端点及素数步长实现；有限单项式 $F_3$ 模式作为推论得到 | `PAPER-AUDITED`；一般有限复杂度版本依赖 Green–Tao–Ziegler 后续结果 |
| [F3-HIER-1 / 2 / 3](docs/proofs/f3/product_hierarchy/theorem.md) | 对任意 $q=3^s$，固定 $q$ 个素数端点的全部总次数 $<q$ 单项式 $F_3$ 数据（允许重复因子），而总乘积深度可取任意 $R\ge k+s$；系数和模 $3$ 决定最高阶锁死或开放；普通族与末点移动族拥有相同全素数计数主系数但不同最高阶分布 | `PAPER-AUDITED`；一般 $q$ 使用完整有限复杂度素数线性形式理论 |
| [F3-ROOT-1 / 2 / 3 / 4](docs/proofs/f3/two_root_process/theorem.md) | 平移配对乘积序列由两个简单三进根精确控制；给出完整联合尾律、区段层级计数、深度序列到参数的显式反演，以及六位置模 $5$ 障碍与 $d=5r$ 后七素数模式 $(3,4,2)$ 的比例 $2/729$ | `PAPER-AUDITED`；局部部分为二次多项式/Hensel 论证，全素数扩展使用一般有限复杂度素数定理 |
| [F3D-POLY-1 / 2 / 3 / 4](docs/proofs/f3d/polynomial_realization/theorem.md) | 对 $F_{3,D}(n,d)=v_3(n+d)-v_3(n-d)$：给出四次精确层检测器；完全分类固定整数多项式对可实现的单输入函数为“两端最终整数仿射”；证明层平移、绝对值、取正部、精确零层检测的最低次数分别为 $1,2,3,4$，并排除 $t^2$ 与固定双输入 $F$ 乘法器 | `PAPER-AUDITED`；依赖标准三进赋值、Hensel 与完备赋值域扩张唯一性，无新增 Lean 证明 |
| [F3D-MULTI-1 / 2 / 3 / 4](docs/proofs/f3d/multivariate_tropical/theorem.md) | 多输入 $F_{3,D}$：二次判断 $F>0$；固定多项式实现 min/max、批量最小值与第一极小位置；完全分类任意固定有限输入的全域可实现函数为有限整数热带表达式；所有可实现函数具有统一 Lipschitz 界，因此无界条件开关不可实现而固定幅度开关可实现 | `PAPER-AUDITED`；依赖三进赋值与有限 Lagrange 插值，无新增 Lean 证明 |
| [F3-MOM-1 / 2 / 3 / 4](docs/proofs/f3/prime_depth_moments/theorem.md) | 固定共享根全素数族中：一致尾界与乘积单射给出更强极深尾；指数加权收敛范围提升到 $\eta<1/(q-1)$；协方差恢复根距离；有限根树给出多元有理概率生成函数，并在 $|z_i|<3^{1/(q-1)}$ 的紧多圆盘上得到全素数生成函数一致收敛 | `PAPER-AUDITED`；以前序固定形状素数主项/固定精度分布为输入，新增 Selberg 尾控制、唯一分解尾界、矩传递与生成函数证明 |
| [F3-PEAK-1 / 2 / 3 / 4](docs/proofs/f3/effective_peak_separation/theorem.md) | 固定普通整数双根轨道中，第二极值具有全范围有效的 (log_3N+O(1)) 界；给出双峰整除分离、根反射定位、完整 (3^T) 区段剔除恒等式、负整数迹直方图及超临界峰有效 (O(loglog X)) 稀疏界 | `PAPER-AUDITED`；核心为初等整数/三进证明，Hensel 只用于任意高孤峰构造 |
| [F3D-DEG-1 … 6](docs/proofs/f3d/degree_tensorization/theorem.md) | 固定整数多项式实现的总次数理论：独立输入截面次数下界可相加；有符号和外套一元函数精确张量化；(min/max) 最低 6 次，而 (kmin/kmax) 在 (kge2) 时最低 (2k) 次；另有不可除 (k) 与 (p=2) 低次检测差异 | `PAPER-AUDITED`；依赖 F3D-POLY / F3D-MULTI 的书面接口，无新增 Lean 证明 |
| [F3-WIN-1 … 6](docs/proofs/f3/sliding_windows_covariance/theorem.md) | 固定整数双根轨道的滑动窗口结构：精确双峰容量、完整二点联合尾、所有窗口最佳第二峰、统一单峰剔除律、平移协方差闭式，以及“协方差恢复 $d$ 但不恢复 $n$”的相位丢失定理 | `PAPER-AUDITED`；核心为初等三进/剩余类证明，结式文献仅作背景定位 |
| [F3D-TERN-1 … 6](docs/proofs/f3d/ternary_minima_norm_forms/theorem.md) | 三输入最小值的精确次数谱 $9,10,9$；两倍最小值具有额外分母代价；有限域范数给 $k\ge m$ 时 $\mathfrak d_m(k)=mk$；分组范数给一倍 $m$ 输入最小值的 $O(m^{3/2})$ 上界 | `PAPER-AUDITED`；依赖 F3D-DEG 的次数下界与经典有限域范数/低次数零点背景，无新增 Lean 证明 |
| [F3-REC-1 … 5](docs/proofs/f3/prime_depth_reconstruction/theorem.md) | 共享根深度的有限观测恢复：第一次不等观测就是精确根距证书；给出完整矩阵恢复等待时间、$3^L$ 被动辨识下界、截断深度精确恢复，以及三个等距根的停止时间闭式 | `PAPER-AUDITED`；证书正确性为确定性三进论证，概率部分只使用局部采样与固定精度素数分布 |
| [F3D-STABLE-1 … 5](docs/proofs/f3d/interval_detectors_stable_degree/theorem.md) | 任意有限整数区间在 $p=3$ 下有四次最优的增益 1/2 检测器；所有两端最终常值函数的放大最低次数存在稳定极限，并由射影剩余类核矩阵逆的 $\ell^1$ 范数给出；有限层集合具有显式指数相互作用公式，连续区间在固定层数下唯一最省 | `PAPER-AUDITED`；依赖标准 $p$ 进射影弦距/剩余树背景、Hensel 与有限矩阵构造，无新增 Lean 证明 |

F3-PAT-1 可以额外要求 $n\equiv5,d\equiv1\pmod{729}$，且 $n,d$ 同时超过任意给定下界。该结论保留可变步长，不包含固定 $d=1$ 的无穷性。

F3-HI 在 $k=1$ 时给出固定偏移 $(18,54)$：六个低阶值锁定为 $(1,1,1)$ 与 $(-1,-1,-1)$，而三因子深度的极限比例为 $1/2,1/3,1/9,\ldots$。这些结果同样保留可变素数步长，不推出固定间距素数簇。

F3-PAT-1：[PDF 版](docs/proofs/f3/four_prime_construction/paper.pdf) · [完整证明](docs/proofs/f3/four_prime_construction/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/four_prime_construction/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/four_prime_construction/formalization.md)

F3-HI：[PDF 版](docs/proofs/f3/higher_interactions/paper.pdf) · [完整证明](docs/proofs/f3/higher_interactions/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/higher_interactions/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/higher_interactions/formalization.md)

F3-HIER：[PDF 版](docs/proofs/f3/product_hierarchy/paper.pdf) · [完整证明](docs/proofs/f3/product_hierarchy/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/product_hierarchy/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/product_hierarchy/formalization.md)

F3-ROOT：[PDF 版](docs/proofs/f3/two_root_process/paper.pdf) · [完整证明](docs/proofs/f3/two_root_process/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/two_root_process/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/two_root_process/formalization.md)

F3D-POLY：[PDF 版](docs/proofs/f3d/polynomial_realization/paper.pdf) · [完整证明](docs/proofs/f3d/polynomial_realization/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3d/polynomial_realization/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3d/polynomial_realization/formalization.md)

F3D-MULTI：[PDF 版](docs/proofs/f3d/multivariate_tropical/paper.pdf) · [完整证明](docs/proofs/f3d/multivariate_tropical/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3d/multivariate_tropical/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3d/multivariate_tropical/formalization.md)

F3-MOM：[PDF 版](docs/proofs/f3/prime_depth_moments/paper.pdf) · [完整证明](docs/proofs/f3/prime_depth_moments/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/prime_depth_moments/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/prime_depth_moments/formalization.md)

F3-WIN：[PDF 版](docs/proofs/f3/sliding_windows_covariance/paper.pdf) · [完整证明](docs/proofs/f3/sliding_windows_covariance/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/sliding_windows_covariance/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/sliding_windows_covariance/formalization.md)

F3D-TERN：[PDF 版](docs/proofs/f3d/ternary_minima_norm_forms/paper.pdf) · [完整证明](docs/proofs/f3d/ternary_minima_norm_forms/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3d/ternary_minima_norm_forms/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3d/ternary_minima_norm_forms/formalization.md)

F3-REC：[PDF 版](docs/proofs/f3/prime_depth_reconstruction/paper.pdf) · [完整证明](docs/proofs/f3/prime_depth_reconstruction/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/prime_depth_reconstruction/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/prime_depth_reconstruction/formalization.md)

F3D-STABLE：[PDF 版](docs/proofs/f3d/interval_detectors_stable_degree/paper.pdf) · [完整证明](docs/proofs/f3d/interval_detectors_stable_degree/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3d/interval_detectors_stable_degree/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3d/interval_detectors_stable_degree/formalization.md)

F3-PEAK：[PDF 版](docs/proofs/f3/effective_peak_separation/paper.pdf) · [完整证明](docs/proofs/f3/effective_peak_separation/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3/effective_peak_separation/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3/effective_peak_separation/formalization.md)

F3D-DEG：[PDF 版](docs/proofs/f3d/degree_tensorization/paper.pdf) · [完整证明](docs/proofs/f3d/degree_tensorization/proof.md) · [引理 DAG 与审计记录](docs/proofs/f3d/degree_tensorization/scaffolding.md) · [形式化映射及阻塞项](docs/proofs/f3d/degree_tensorization/formalization.md)

## 猜想地图（未证明）

令 $\mathcal B=\{p>2:p\text{ 为素数且 }\Omega(p-1)=\Omega(p+1)\}$。这里是 **Ω 计重个数平衡**，不是质因数求和的 S 平衡。默认允许 $p=q$，不要求两个加数的平衡级数相同。

**以下不是已证定理；有限验算不是无限范围证明，也没有作为 Lean 公理加入。**

| 编号 | 猜想 | 精确陈述 | 当前证据与状态 |
|---|---|---|---|
| [OBG-1](docs/conjectures/omega_balanced_goldbach.md#obg-1) | **充分大偶数覆盖** | 存在 $N_0$，每个整数 $N\ge N_0$ 都有 $p,q\in\mathcal B$ 使 $2N=p+q$ | 未证明；有限计算支持 |
| [OBG-2](docs/conjectures/omega_balanced_goldbach.md#obg-2) | **显式起点版** | 每个整数 $N\ge259\,299$ 都有这样的表示，即覆盖全部偶数 $2N\ge518\,598$ | 未证明；已验算每个偶数 $518\,598\le2N\le10^8$ |
| [OBG-3](docs/conjectures/omega_balanced_goldbach.md#obg-3) | **不同加数加强版** | OBG-2 中进一步要求 $p<q$ | 未证明；同一区间有限验算仍成立 |

**OBG-3 ⇒ OBG-2 ⇒ OBG-1**。一亿以内的 3,088 个不可表示偶数最大为 518,596，不代表一亿以外没有例外。“覆盖全体偶数”已被 100 等反例否定，不列为开放猜想。详见[猜想档案与验算范围](docs/conjectures/omega_balanced_goldbach.md)。

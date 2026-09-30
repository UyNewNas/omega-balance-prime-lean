# F₃ 外部查重复用记录

本记录区分源码核验、外部构建报告与本仓库精确提交的内核验证。未找到表示下述已查范围内未找到；访问失败不表示定理不存在。

## 2026-09-30：F3-PAT-1 局部算术（PAT-L1–3）

- 本仓库基线：`b4c14823d9a97a45770ed42379673d39b5295be6`；证明来源：`4c532a866ad60bbe0492a928b41fe1fa1c1766e6`，后续 PDF 整理不改变局部结论。
- 目标：对 `1<n`、`0<d`、`n≡5,d≡1 (mod 729)`，四点值 `(1,-1,-1,-1)` 与三个乘积值 `(3,5,3)`；无素性假设，也不作全局素数存在性推论。
- 锁定 mathlib：[`5ed2965256430c3649e86755f9576b54eca72435`](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435)，Lean `v4.34.0`。已读取实际声明及证明体，许可证为 Apache-2.0。
- 查询：GitHub `padicValNat mod`、`padicValNat eq_of`、`valuation add_eq_min`、`map_add_eq_min`、`f3_pat1_pattern_of_mod729`；锁定源码与当时最新主线 `a79b0d211ae2978372e1408be7162e0710f589da` 对照。最终七值定理在已查范围未找到现成实现。

| 缺口 | 已核验复用源 | 前提与决定 |
|---|---|---|
| 同余传递整除 | [`Nat.ModEq.dvd_iff`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Nat/ModEq.lean)；blob `89b9538904c468cdd94f8cd1613fb1fea8c9700d` | `a≡b [MOD m]`、`d∣m` 给出 `d∣a ↔ d∣b`；直接复用 |
| 幂整除与赋值 | [`padicValNat_dvd_iff_le`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean)；blob `09e4fe43670b683a56a386ff184228b0894fe2d3` | 素数实例及非零输入；直接复用，不能对总化零点遗漏前提 |
| 项目赋值桥梁 | `valuation_eq_padicValNat` / `v3_eq_padic` | 保留项目 `v3` 定义，仅薄适配 |
| 符号与有限运算 | 项目 `f3_of_mod_three_one/two`、mathlib `Nat.ModEq` 运算 | 补未覆盖局部组合；不引入新依赖 |

本地未安装 Lean/Lake，构建、公理传递闭包及回归由现有 GitHub Actions 的精确提交验证。源码读取及有限检查不是内核验证；状态以 PR 的精确 SHA 与运行链接为准。

## 2026-09-30：PAT 全局依赖边界

查找最终等价目标优先：GitHub `Green Tao`；网络/社区 `Lean formalization linear equations in primes`、`Lean Green-Tao formalization`、`site:leanprover.zulipchat.com Green Tao primes`。已查范围未核验到可访问、可重用的 GT10 Corollary 1.7 复杂度至多 2 素数线性形式渐近的完整 Lean 源码。

[`lean-eval-submissions/results/vilin97.json`](https://github.com/leanprover/lean-eval-submissions/blob/main/results/vilin97.json) 记录任意长素数等差数列的接受结果，包括 `Vilin97/lean-eval-green-tao@0c5d3337c3ebb59c318ab9030e31b835826141f8` 与 `AxiomMath/lean-eval-submissions-final@b092f7455ac0cf0c405e42fbb669ef8144de9fd9`，但标记 `public:false`；前者源码读取返回 404。源码、许可证、精确前提和传递信任未能核验。任意长等差数列也不自动给出本项目指定同余条件的二参数渐近。

决定：保持 EXT-GT2 为外部未解决依赖；不添加文献公理或同名假设，不将 `PAPER-AUDITED` 降称猜想，也不将局部模式称为主结果 `LEAN-PROVED`。先形式化已核验复用范围内的 PAT-L1–3。

## 2026-09-30：复用已验证 COR / DEN / LOG 栈

最终目标优先检查开放 PR 的真实声明，避免重复实现：本仓库 [PR #28](https://github.com/UyNewNas/omega-balance-prime-lean/pull/28) 的固定源 `66b8e8380d240868c5fdd784eeb6aedb966cae3a` 已有完整整数相关极限、正幂三平移均方极限、正负素数密度与17倍升层比例、真正三进 log 级数及同态/赋值桥梁。读取了实际 Lean 定义、假设和证明体；不是以 PR 标题或旧任务状态作证据。

源版本 [Lean run 36309723481](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36309723481) 成功，597 条声明公理/覆盖通过，93 个项目文件无禁用项。该运行只证明源版本，不能代替当前 master 合并后的验证。

采用真正三方合并，保留 master 新证明包、PAT-L1–3、ROOT-4 修正；仅 import/Audit/任务账本冲突作并集处理。锁定 Lean/mathlib 不变，ANT 使用原源固定 `099d3726c2c74841024110ec1dd9902f7ef36e9e`；不改上游仓库。新组合树要求重新构建全部 601 条声明并核对实际解析依赖清单。已验证历史 API 保留。

RUN 的有限 CRT、最大化、顺序块和条件组合接口一并保留，但无条件素数产生器仍未完成。PR #29 固定 `9033636693d0f713c9cb6e1bc5d13149052b812b` 的 [Lean run 36467303064](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36467303064) 构建失败：`lean-proofs-latest` 与 `analytic_number_theory` 重复模块所有者，以及锁定版本的 Sobolev/BoundedGaps API 不兼容；下游回归和公理检查未运行。该失败栈不导入本次组合候选，不以文献公理或新增假设填补无条件 RUN。

源 CI 解析依赖已从成功 run `36309723481` 的 artifact `10929140097` 下载，ZIP SHA256 与 GitHub 报告一致：`31e70f907bde8c1e375f5acfd3384771d616249091a7f45c68fbb685e21cc0e1`。本次提交该实际 `lake-manifest.json`：mathlib `5ed2965256430c3649e86755f9576b54eca72435`、ANT `099d3726c2c74841024110ec1dd9902f7ef36e9e`、LeanArchitect `78dd66840d3efe8c824c699fc03381cec817c271`、Cli `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`；其余传递固定版本按完整清单保留。不是手工猜测 Lake 的解析结果。ANT 原源使用4.33rc1/mathlibe4c91783，但上述消费端4.34/5ed组合已有真实编译证据；当前组合仍待新CI。ANT许可证Apache2，依赖源码闭包审计继续独立记录。

ANT源闭包复核完成：从`PrimeNumberTheoremAnd/Consequences.lean`递归到9个本包模块，379391字符；使用本仓库支持嵌套注释与字符串擦除的禁用项扫描，0命中。范围排除锁定Mathlib、Architect及Batteries的实现源码。WeakPNT_AP的前提仅q≥1、a.Coprime q、a<q，不含目标重述假设；最终COR/DEN/LOG声明在历史成功日志中逐条只依赖标准3公理。证据摘要见`reports/f3_ant_source_scan.json`；本组合CI仍会实际执行全601条公理审计。

## 2026-09-30: RUN dependency compatibility repair candidate (not kernel-verified)

This candidate preserves Lean `v4.34.0`, mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and ANT
`099d3726c2c74841024110ec1dd9902f7ef36e9e`. It ports the actual PR #29
adapter and three real-exponent cutoff lemmas onto the PR #45 source tree,
preserving the four local PAT-1 theorems and all prior public declarations.
There are 606 project theorem declarations and one separately mandatory
external producer audit entry. No successful build is claimed in this record.

### Exact producer and bounded reuse search

The imported theorem is
[`MaynardBFT.consecutive_primes`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Util/MaynardTao/BFT/Result.lean).
It provides arbitrary positive block length, arbitrarily late starting index in
the full `Nat.nth Nat.Prime` enumeration, a prescribed reduced residue class,
and diameter at most `q * C`, with `C` chosen before modulus and residue. The
OmegaBalance adapter preserves that order of quantifiers and derives all
nonzero F3 levels, with bound `f3RunModulus c * C`. It does not replace
full-prime consecutiveness by adjacency in a selected subsequence.

The 2026-09-30 source search read all 77 reachable plby modules and all 573
reachable BoundedGaps modules at immutable SHAs. The source closure has no
`PrimeNumberTheoremAnd`, `APAP`, `AINTLIB`, `Waring`, `leancert`, Comparator,
or `ErdosProblems.Axioms` import. Its remaining imports are Mathlib or Lean.
Queries covered `MaynardBFT`, Shiu, BFTB, consecutive primes, prescribed
residue classes, and Lean 4.34 compatibility, including plby branches/PRs,
FormalPantheon, PrimeGapsLib, and gotrevor forks. This is a bounded search,
not a universal absence claim. FormalPantheon main at
`e2a77fe164e54b205d9716e92de8d80e05aac342` still supplies the weaker final
bounded-pair interface and an older toolchain. PrimeGapsLib main
`1faa7b14e82ddebc2772dfb9153922f01b106477` supplies a conditional bounded-gap
result; PR #11's unconditional 246 result targets Lean 4.33.1 and does not
replace the arbitrary-length, prescribed-class BFT producer.

The [gotrevor ownership fix](https://github.com/gotrevor/lean-proofs/commit/8b7630fef471b6ac8685f1830f8b0288e5b9f4f1)
and [root-package hook fix](https://github.com/gotrevor/lean-proofs/commit/ff0f9f63d7175dfa07b44a9c6a7148ca60a61676)
are relevant packaging precedents, but their 4.33.1 pins are not adopted.
The original PR #29 failure is recorded at
[run 36467303064](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36467303064),
head `9033636693d0f713c9cb6e1bc5d13149052b812b`, job `109080485402`.
It failed during the build, before the previously latent audit-coverage
rejection of its external producer entry could execute.

### Small source-preserving adapter

`python3 scripts/prepare_run_dependencies.py update` is the supported update
entry point. It restores only its recognized 4.34 proof edits, invokes a real
`lake update` so all nine original upstream patch checks/applications run,
then reapplies exact-hunk, full-file SHA256-guarded compatibility edits. Unknown
source edits, wrong checkout SHAs, unexpected root pins, or a mismatched
resolved Lake manifest fail closed. No fuzzy patching or proof-source copying
into this repository is used. Cached reruns follow the same checked sequence.

Only the downloaded plby Lake library declaration block is narrowed: a
`F3RunProducer` library has empty roots and exactly 77 one-module globs. This
uses the actual Lean 4.34
[`LeanLibConfig`](https://github.com/leanprover/lean4/blob/v4.34.0/src/lake/Lake/Config/LeanLibConfig.lean)
`isLocalModule`/`isBuildableModule` behavior. All original requirements and
post-update checks remain. The next Lake invocation loads the modified
configuration; changing the file is not alleged to change an already-loaded
Lake graph. ANT remains the sole owner of `PrimeNumberTheoremAnd`. CI uses a
compatibility-sensitive cache key. The source/pin check also rejects stale
embedded PNT build artifacts that could otherwise shadow ANT on Lean's search
path; only the indicated generated upstream build cache should then be removed.

The locked mathlib APIs used for the proof-only compatibility changes are:

- `Finset.prod_le_prod₀`, `one_le_prod₀`, `prod_le_one₀`, and
  `prod_le_prod_of_subset_of_one_le₀` for old nonnegative ordered-ring proofs
  ([locked source](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean))
- `logDeriv_fun_mul`, `logDeriv_fun_div`, `logDeriv_fun_prod` for existing
  lambda-shaped goals
  ([locked source](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Analysis/Calculus/LogDeriv.lean))
- Explicit `Mathlib.Analysis.Analytic.Order` and
  `Mathlib.Analysis.Meromorphic.Basic` imports for existing, still-supported APIs

These are proof-body/API/import changes, not theorem statement changes or new
mathematical assumptions. No artificial `MulLeftMono ℝ` instance is introduced.
The project source audit, exact declaration coverage, executed standard-axiom
check, finite checks, and kernel regressions remain required. The only audit
coverage extension names exactly `MaynardBFT.consecutive_primes` as a required
entry; missing, duplicate, or unknown entries still fail, with focused tests.

### Provenance and verification boundary

FormalPantheon `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1` has Apache-2.0
licensing; source and authorship headers are preserved. plby's
`src/latest/LICENSE` licenses some externally sourced files, but a blanket
license grant for its authored BFT closure was not verified. The dependency
remains an immutable upstream checkout with narrow compatibility instructions;
it is not wholesale vendored or relabeled Apache. This avoids a new ownership
claim but does not itself resolve upstream license scope.

No Lean executable is installed in the dot cloud checkout. Python source,
hunk, idempotence, and negative tests are local evidence only. CI must first
resolve and verify actual manifest/checkouts, build the exact producer, then
build the project, execute all 607 axiom entries, and pass the remaining
repository gates at the exact candidate head. CI preserves the actual
`lake-manifest.json` and `reports/f3_run_dependency_resolution.json` as
artifacts. The committed manifest now reproduces the actual dependency resolution
from failed PR #29 run `36467303064`, artifact `10990772124`, without treating
that failed proof build as verification. Its exact bytes have SHA256
`89f5ab9a58281ab317598d35eee76eb2cc2b547c7fa8d2ab10eef9894a5a1267`; the
downloaded artifact archive has SHA256
`a53693cdf5ca68f7ffaa938543a05e103ef64a93a194b24e70d36eac442ef84c`.
Lake serializes the producer Name as `«lean-proofs-latest»`; the validator uses
that one explicit `manifest_name`, rather than stripping quotation marks or
accepting aliases. All four source packages retain exact revision, URL, and
subdirectory guards. A new update must reproduce the complete observed manifest
byte-for-byte, in addition to matching actual checkout SHAs. Regression tests
cover the actual manifest, every pin field, missing/duplicate package entries,
and incorrect quoted/unquoted aliases. RUN remains unverified until exact-head
CI passes; additional downstream API failures must be repaired without changing
pins.

### 2026-09-30: symbolic bound repair after the first RUN producer build

The actual first candidate build at head
`0b13f311284e16d97f2dbdb0b93eded09a5c5552`,
[run 36663110201](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36663110201),
job `109721941998`, passed dependency preparation and reached the producer's
source closure. Its sole reported failed target was
`ErdosProblems.Erdos6.BFTExtraction`: line 55's `hzmax` proof and the enclosing
private declaration at line 24 failed the kernel's `Nat.pow` evaluation guard.
The full producer, project build, and executed axiom audit therefore did not
pass; the previously failing build is not reused as proof verification.

At the immutable producer SHA, `Erdos6.Maynard.largeK = 2 ^ 512`. The bound
`2 ^ largeK` must stay symbolic. Lean 4.34's actual
[`get_count_arg` kernel implementation](https://github.com/leanprover/lean4/blob/v4.34.0/src/kernel/type_checker.cpp#L305-L313)
rejects numeric power evaluation when the exponent exceeds `UINT_MAX`.
The failing `omega` proof was unnecessarily requesting arithmetic reflection
for a bound already implied by two local inequalities.

The additional guarded hunk replaces only that proof body:

```lean
  have hzmax : z ≤ n + 2 ^ largeK :=
    Nat.le_trans (Nat.le_of_lt hzhi) (Nat.add_le_add_left hbmax n)
```

It composes `z < n + b` with `b ≤ 2 ^ largeK`, without evaluating the power.
The exact [locked Nat API](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/Nat/Basic.lean)
provides `Nat.le_of_lt` and `Nat.add_le_add_left`; `Nat.le_trans` is also used
there. No theorem signature, constant, assumption, kernel setting, or axiom
allowlist changes. The file's original, pre-patch, and prepared SHA256 guards
are updated; there are now 41 managed files. A focused regression asserts the
single symbolic-proof hunk and unchanged bound statement. Offline application,
reverse application, repeated application, and all 650 prepared source hashes
pass. This is still only source/tooling evidence: the repaired exact head must
be rebuilt and audited by CI. The upstream authored-source license scope remains unconfirmed; see the
[attribution and contact notice](f3_third_party_sources.md). Technical work
continues with that uncertainty explicitly recorded; all mathematical and
engineering merge gates remain mandatory.

### 诊断顺序与冷构建时间

已对实际来源导入图计算：BFTExtraction只闭包到48个非mathlib模块，全producer闭包为650个。因此CI和verify先单独构建该已知失败的有限提取模块，再构建完整producer与全部项目，任何阶段失败仍阻止后续成功声明。第一轮冷构建耗时约26分钟后在唯一已知节点失败；为完整producer及后续项目/审计留下时间，将同一job超时从30改为60分钟，不删除、跳过或削弱任何证明/源码/公理门禁。日志分别保留run-extraction.log和run-producer.log。
## 2026-09-30：相对全部素数计数与 REC 确定性证书

密度最终目标先查：GitHub `f3PrimePosLevel relative density` 在已查范围无匹配；本仓库所有分支标题/现有API核对后，仅17倍接口已用实际计数比。薄复用既有 `f3PrimeAPCountingReal_normalized_tendsto` 的模1特化（0与1互素）得到真实全素数计数PNT，复用 `Filter.Tendsto.div` 及 `div_div_div_cancel_right₀` 将三个x/log x极限转换为实际素数计数比例，无新分析栈。

锁定mathlib5ed2965实际源码：`Mathlib/Topology/Algebra/GroupWithZero.lean` blob `ad409ad08d53ad030bfd8f29cb2825a19b33872e` 的 `Filter.Tendsto.div` 要求分母极限非零；`Mathlib/Algebra/GroupWithZero/Units/Basic.lean` blob `b3148d9bd8bac8cbc1c64edf40b1c0bbb61f2916` 的商约消要求公共除数非零。已分别读完整声明及证明，最新默认源同API仍在（blob4ef88673与9fd9e942），不升级。通过PNT极限1证明分母最终非零，有限初段不强加全局假设。库为Apache2，当前代码独立CI待执行。

REC最终目标在已查GitHub精确名 `rootDepth_min_eq_distance_of_ne` / `truncatedDepthCertificate_sound` 无匹配；直接复用锁定 `AddValuation.map_sub`、`map_add_of_distinct_val`、`map_neg`、`map_sub_swap`、`top_iff`/`ne_top_iff`（`Mathlib/RingTheory/Valuation/Basic.lean` blob73f71ae8fde499401b25db33fd2d826eecfb9c0b），以及真正 `Padic.addValuation : AddValuation ℚ_[3] (WithTop ℤ)` 和 `.apply`（PadicNumbers blob79040472922216be2c0d66793e3b2a3965347e9c）。有限精度只用 `Mathlib/Order/MinMax.lean` 的已读 `min_lt_min_left_iff`、`min_eq_right_iff`。保持∞零点、实际p-adic域和源模型b+R；不以有理数弱化或概率假设代替目标。

### 2026-09-30: remove reflection throughout the private extraction proof

The next exact build, head `939f8600`,
[run 36665897371](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36665897371),
job `109730369373`, passed the earlier `hzmax` location but still rejected the
enclosing private declaration at line 24 with the same `Nat.pow` guard. The
one-line repair was therefore insufficient. Other `omega` invocations in that
declaration still had the closed giant bound in their local context; the log
does not identify which generated subterm caused the remaining rejection.

The guarded replacement now removes every arithmetic-reflection invocation in
that one private declaration. Fin index bounds use `Nat.lt_of_succ_lt`; the
power comparison uses `Nat.pow_le_pow_right` and `Nat.succ_le_of_lt`; lower and
upper interval bounds use direct order composition; and the final index
contradiction uses `Nat.not_lt_of_ge`. Equality transport and the locked
[`OrderIso.apply_symm_apply`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Order/Hom/Basic.lean#L842-L843)
replace unnecessary simplification. The proposition, original hypotheses,
`largeK`, and `2 ^ largeK` span are unchanged; only proof terms change. There
is no new declaration or opaque substitute. Original source SHA guards and
all kernel safeguards remain. Focused tests check the unchanged proposition
(up to proof-irrelevant Fin bounds), absence of reflection tactics, exact
symbolic terms, and all 41 patch round trips plus 650 prepared source hashes.
These are offline checks; the new exact-head finite-extraction checkpoint,
producer, library, and full audit still have to pass actual CI. The current
source-attribution notice is preserved.


### 2026-09-30: generic finite-extraction helper and connector recovery

Exact head `51478e43277c7b3072fb50d57d96655ffe473011`, push run
[36667342374](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36667342374)
(job `109734723911`), still failed the private theorem at line 24 after all
arithmetic reflection in that declaration had been removed. Thus reflection
alone does not explain the kernel rejection. The precise definitional-equality
reduction causing the closed giant power to be evaluated remains unlocalized.

The next narrow replacement proves a separate private helper over free
`H : Finset ℕ` and `B : ℕ`, with a proved-use premise bounding all shifts by B.
Its proof contains no powers or fixed tuple constants. The original theorem
retains its exact proposition and original hypotheses (only proof-irrelevant
Fin index terms differ), and instantiates the helper with the unchanged
`largePowerTuple` and `2 ^ largeK`. The required shift bound is actually proved
parametrically in K before specialization. No kernel option, axiom allowance,
public target, or numerical constant changes; no dependency module is pruned.

The local candidate was committed as `f60a1ee82bb9d66be6c018b606c6bcd99b109079`
before the cloud execution environment went offline. This publication does
not claim to upload that complete local tree. The complete previously read
replacement and immutable upstream source were reconstructed through the
GitHub connector and checked byte-for-byte by SHA256: original BFTExtraction
`ca1327c93e785659208d3af958f62e05e89ca4930d6a77076d6f99e74c52ff00`,
prepared `8ec558b9450f02553b35aa3d27fc7c850caf5de5923ad84b3a80193c9ee2a579`.
The latter exactly matches the previously recorded local candidate hash.
The manifest changes only this prepared source/guard and records the added
private helper. The focused Python test was reconstructed from its last
published version to check the generic helper and unchanged wrapper signature;
it has not been executed locally in the offline environment. All existing
round-trip, 650-file source-closure, manifest-pin, producer, project, regression,
axiom and coverage gates remain for actual Actions validation. The two bot
regenerated PDF blobs are restored to the already reviewed master versions.
The full RUN target remains unverified until the exact candidate passes.

## 2026-09-30：REC-L5 目标优先查重复用

目标先固定为命题 2.2 的**确定性有限观测矩阵恢复和阈值根簇**，不是采样律、
信息论下界、全素数传递或重新开发 p-adic 赋值。源码基线 master
`5a622dc4e90db25dbc21f926de873be17372ed39`；paper proof 最后数学来源提交
`b4c14823d9a97a45770ed42379673d39b5295be6`（PR #41），proof blob
`ef55306b0c00adc68cfd8407440a4bdd46e6de10`。本轮完整重读 theorem/proof/scaffolding/formalization。

实际查询（2026-09-30）：GitHub code `rootDistanceMatrix depthCertificate`、
`rootClusterSetoid depthCertificateMatrix`、`ultrametric equivalence Setoid`、
`findSome? eq_some`、`ultrametric root recovery`；mathlib PR `ultrametric reconstruction`；
全局 PR `p-adic root cluster matrix reconstruction`；公开网页
`Lean ultrametric reconstruction root distance matrix valuation certificate`、
`Lean mathlib ultrametric Setoid balls equivalence relation`、
`"Corregidor" "Martínez-Pérez" "Lean"`。已查范围未找到等同最终 F3 目标的 Lean 定理；
无关数值根隔离代码与非 Lean 材料不是可复用证明，不作全网不存在声明。
书面引用 [Corregidor–Martínez-Pérez, arXiv:2003.10239](https://arxiv.org/abs/2003.10239)
已核对论文入口；一般 metric-basis 背景不替代本目标源码证据。

直接复用/薄适配清单：

| 来源、固定版本、源码证据 | 精确 API 与适配决定 |
|---|---|
| 本项目 `OmegaBalance/F3RootCertificates.lean`，PR #46 已验代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b` | 复用 `depthCertificate_sound`、`rootDepth_min_le_distance`、`rootDistance_ne_top`；既有 12 个证书定理保持不变，不复制不重证 |
| [Lean v4.34.0 `Init/Data/List/Find.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Find.lean)，blob `d8c0b839d8f24f52d21d7a0f34a5be621894dff8` | `List.findSome?`；`List.findSome?_eq_some_iff` 给出首个成功观测和之前全为 none 的前缀；`List.exists_of_findSome?_eq_some` 提取真实成员；`List.findSome?_eq_none_iff` 刻画未知。实际读取精确声明及证明；直接应用，不新增递归扫描基础 |
| [mathlib 5ed2965 `Data/Setoid/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Setoid/Basic.lean)，blob `90500f54e13f5572f222575d910bdccbbd4dd3ed` | 用原生 `Setoid` 表示根簇分区，用其关系包含顺序表达高阈值细化；不新建通用分区/树框架 |
| [mathlib 5ed2965 `RingTheory/Valuation/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/RingTheory/Valuation/Basic.lean)，blob `73f71ae8fde499401b25db33fd2d826eecfb9c0b` | 直接用已读 `AddValuation.map_zero` 和 `map_sub_swap`，传递性复用项目中实际 `Padic.addValuation` 的最小值界。保留 `WithTop ℤ` 及命中根时的 ∞ |
| [mathlib 5ed2965 `Topology/UniformSpace/Ultra/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Topology/UniformSpace/Ultra/Basic.lean)，blob `9a201e0bc4fc8412b18b6f3f6ca5fce0131d6d26` | 阅读完整文件：通用超度量一致空间 API，仍注明 valued-ring 超一致性桥接 TODO；不导入该较大拓扑接口来包装三个初等关系律 |

实时核对上述 Lean `Find.lean` 与 mathlib `Ultra/Basic.lean` 的最新默认分支，返回 blob
与所查锁定版本相同；已查 mathlib PR 无等同目标候选。库源码为 Apache-2.0，
当前只调用原依赖的接口，没有移植外部证明文件或增添新包。最终声明的定义域为真实
`ℚ_[3]`；一般适配器允许任意 p-adic 点，纸面 wrapper 显式保留 `F3SharedRootConfig`、
样本为单位、公共正基础深度及逐对真实根距固定。没有假设扫描所得矩阵等于目标，
没有将单位域概率律写作前提。

结果：`F3RootReconstruction.lean` 的10条新声明已由精确代码 c2fe3c4 的 push36667493101 和 PR36667536541 完整CI核验：630条只含标准公理、97文件无逃逸、精确覆盖及全部构建/回归门禁通过。最终文档头另验CI，REC完整概率主结果仍未完成。
[完整映射与剩余项](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l5-有限矩阵与根簇已通过精确-ci)。

## 2026-09-30：REC-L11 / 截断 REC-L5 增量复用门

目标优先固定为定理 2.6 的**确定性有限截断矩阵扫描、恢复 iff 与 t≤H 根簇**。
初次实现前完整重读 theorem/proof/scaffolding/formalization 四件套；本包不存在
`lean_scaffolding.md`，实际 DAG 文件为 `scaffolding.md`。数学来源为
PR #41 `b4c14823d9a97a45770ed42379673d39b5295be6`，proof blob
`ef55306b0c00adc68cfd8407440a4bdd46e6de10`。原源码基线 cc4eadf 与 PR #49 代码
c2fe3c4 同树；工作区更换后恢复基线为已合入 PR #49 的 master
`f50d23667628c868610c34d5157fe9bbd21357d3`，不修改既有完整精度模块。

初次实现时已执行的目标查询：GitHub code `truncatedDepthCertificateMatrix`（无结果）、
`truncated ultrametric reconstruction`（返回非目标论文/文本，无已核验等价 Lean 实现）；
mathlib 全状态 PR `ultrametric reconstruction`（无结果）；公开网页
`"Lean" "truncated" "root" "certificate" ultrametric` 与
`site:leanprover.zulipchat.com ultrametric truncation reconstruction`。
这些有界检索未发现等同最终目标的可复用定理，不代表全网不存在，也不把无关
“Lean-checked”描述当作目标的已验证实现。恢复时沿用这些保留记录和固定源码证据，
不声称重复执行了外部查询。

直接复用顺序与来源：

1. `F3RootCertificates.lean` 的 `truncatedDepthCertificate`、
   `truncatedDepthCertificate_sound`、`truncatedRootDepth`、`truncatedRootDistance`，
   已验代码 `70becdbf3d7b5ad8169dbcaeebfe08dc3a68f65b`。既有实际 ℚ_[3] / WithTop ℤ
   的单对证明直接调用，不重新建立赋值或截断理论。
2. `F3RootReconstruction.lean`（PR #49 已验代码 c2fe3c4，现已合入 master f50d2366）的
   `rootClusterSetoid`、`rootDistance_threshold_equivalence` 与既有细化接口。
   仅加入 t≤H 的薄 min 比較桥，不能把任意阈值恢复带到截断矩阵上。
3. 初次实现时再次实际读取 [Lean v4.34.0 的 `Init/Data/List/Find.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Find.lean)，
   blob `d8c0b839d8f24f52d21d7a0f34a5be621894dff8`，直接用
   `List.findSome?_eq_some_iff`、`List.exists_of_findSome?_eq_some`、
   `List.findSome?_eq_none_iff`；声明及证明与上一轮固定源码一致。
   不重做泛型列表扫描基础。上一节已核验的最新主线对照、锁定 mathlib
   `Setoid` / `AddValuation` / min API 证据继续复用。

Lean 与 mathlib 许可证为 Apache-2.0；本次仅调用已有依赖，无外部证明文件移植、
无新依赖或版本变更。`hfixed` 是真实距离固定前提，`hcomplete` 是有限观测的
“不同或联合饱和”存在见证；不存在以同名目标假设证明自身的接口。
恢复后的 244 行 Lean 源码 blob 为 `4a24db55453664e08976cd883757912c874f1adb`，
与工作区更换前记录相同；源码守卫与覆盖检查重新通过（98 文件、641 条 exactly once）。
代码564bb498的push36671721342与PR36671762437均已实际全门禁通过，641条标准公理、98源文件及完整覆盖/回归；最终文档头仍另验CI。仅确定性范围已核验，详细声明和边界见
[形式化映射](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l11--截断-rec-l5-有限矩阵已通过精确-ci)。

## 2026-09-30: BFTParameters symbolic checkpoint

Exact RUN head `65e0f5e21bba434aca8624eb04338b0ddb87329b`,
[run 36671388031](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36671388031),
job `109746931058`, successfully compiled the full BFTExtraction checkpoint.
The subsequent producer build failed in BFTParameters at lines 14 and 170
with the same closed huge-power kernel reduction guard. Project build,
regressions and actual axiom checks did not run; RUN remains unverified.

The immutable upstream BFTParameters source at plby/lean-proofs
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e` has SHA256
`bda78b68b8a4ac94189c36ad8dd131b9013dc28cccbd37d69b23563b7435d10a`.
A bounded upstream check found the current file byte-identical; no newer fix
was found. The existing fixed-version Nat order and power APIs suffice.
Two private helpers prove the power bound parametrically in K and interval
subtraction bounds parametrically in B. Original public statements, largeK,
all hypotheses and numerical constants remain unchanged. Four exact guarded
hunks replace only those proof terms; the final contradiction explicitly
eliminates False into the original existential isolation target. Independent
source review caught and corrected that elimination before publication.
Prepared source SHA256 is
`762a6b5e9d74bfd6e5de8d582909a939d22873552e2116c9ff3519733cb740f9`.

The manifest records the 42nd managed file and both private helpers. Exact
forward/reverse hashes, the source guard and 15 focused compatibility tests
pass locally; these are not kernel checks. Actions now builds BFTExtraction
and BFTParameters together before the full producer so another failure here
is reported early. All later producer, project, regression, axiom, source and
coverage gates remain. The precise global definitional-reduction mechanism
is not claimed to be fully localized. The source notice and unconfirmed
authored-source license scope remain accurately recorded.

## 2026-09-30 REC-L3 actual Haar law: target-first reuse gate

Starting tree: master `8548f385e095bf399c27bc3388f8128e4c7fc93c` (641 verified
project declarations). The accepted paper node is REC-L3, proof §1 and theorem
2.1, not a new conjecture. Its actual source normalization was also read at
[prime_product_correlations §3](https://github.com/UyNewNas/omega-balance-prime-lean/blob/a1a724b6083e223ee407046c17dc8c90b036150f/docs/f3_balance_research/prime_product_correlations.md),
blob `0642a3a41c6ce854cb4038250d17d27edff3dfbf`.

Target-first searches included PadicInt Haar measure, p-adic valuation geometric
distribution Lean, padic measure ball, toZModPow addHaar, measure_toZModPow_fiber,
PadicInt volume_closedBall, PadicInt measure IsUnit, firstSuccess geometric, and
mathlib PR / Zulip p-adic Haar equivalents. Current mathlib master was resolved
as `380f2aafb622cb2c1c93dac545b6389083c68c51`; no complete REC law was located in
the inspected sources. This is a bounded negative finding, not universal absence.

Selected minimal closure: Ralf Stephan, in collaboration with Claude Code,
[PadicIntHaar.lean at 7cc2da3f9219e084ee656c096c2055922f4b267c](https://github.com/rwst/lean-code/blob/7cc2da3f9219e084ee656c096c2055922f4b267c/ForMathlib/NumberTheory/PadicIntHaar.lean),
CC0 1.0 Universal. Its complete 100-line source and license were inspected.
Four private helpers plus its public theorem are ported with original attribution
and URL, all renamed to public `OmegaBalance` declarations and individually
registered in Audit. All four imports are mathlib; the external repository's
other potentially axiomatic files are not imported. The actual theorem partitions
all p-adic integers into finite disjoint translated fibers and uses Haar
translation invariance and total mass one; it does not assume ball masses.

Upstream uses Lean4.34.0-rc2 / mathlib169f50d4; this project retains Lean4.34.0 /
mathlib5ed2965256430c3649e86755f9576b54eca72435. Exact source comparisons found
RingHoms, ProperSpace and Haar/Basic identical, and the used PadicIntegers and
Group/Measure APIs unchanged. No dependency is added or upgraded. Exact upstream
commit had zero GitHub Actions runs; this is source compatibility evidence only,
not executed upstream or project kernel verification.

Alternatives read: the same repository's larger ambient `PadicHaar.lean`, and
ImperialCollegeLondon/FLT `eb6df2b018f81920cd48dd510417f0b7790c305e` Haar setup
(Apache-2.0). Neither larger closure is needed. `Padics.Measure.Basic` is
p-adic-valued measure theory and does not prove this real probability law.
An algebraically defined geometric PMF is not an actual Haar pushforward proof.

The local adapters instantiate concrete `addHaarMeasure ⊤`, prove genuine
unit-domain mass 2/3 and normalize its restriction, and bridge actual WithTop ℤ
rootDepth to residue fibers with the zero/infinite case explicitly separated.
[Implementation map](proofs/f3/prime_depth_reconstruction/formalization.md) and
[task ledger](f3_formalization_tasks.md) record exact coverage and open work.
No Lean/Lake executable is present locally; this candidate awaits exact-head CI.

Continuation: root-nullity additionally reuses locked mathlib
`Mathlib/Basic/ENNReal/Inv.lean: ENNReal.exists_inv_two_pow_lt` (inverse powers
of 2 approach 0) and `Mathlib/Algebra/Order/Monoid/Unbundled/Pow.lean:
pow_le_pow_left'`, comparing proved 3^-n fiber masses to 2^-n. Both exact sources
were read at 5ed2965256430c3649e86755f9576b54eca72435. Restriction preserves the
proved singleton zero. Original model wrappers reuse PadicInt.mkUnits/mkUnits_eq;
all assumptions and actual ℚ_[3] roots are retained. Exact layers and unequal
events reuse the already verified rootDepth_min lemmas and actual Haar tails.
The first project run 36675740452 compiled the upstream 5-declaration port, then
failed on local import/complement namespace/numeral cast elaboration. This is
recorded as failure, not a successful full trust audit. Fixed core Omega import
was verified at leanprover/lean4 v4.34.0 src/Lean/Elab/Tactic/Omega.lean.

## 2026-09-30 07:05 UTC：实际 Haar 单次概率内核验证

PR51 代码 dc063232 的 push36681283200 与 PR36681288176 已全部通过：
679 条标准公理声明、104 源文件、精确 Audit 覆盖及全部构建/回归。
六个模块共38条新增声明证明实际单位域归一化、单根尾/层质量、有限根距下
不等深度质量3^-L、原配置包装和无限根点零测。CC0 五声明移植及其全部适配器
现在具有本项目固定 Lean/mathlib 的实际传递公理验证，不再仅为源码兼容猜测。
[精确声明及范围](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30rec-l3-实际-haar-单次概率已通过精确-ci)。
独立等待律/均值、完整有符号差分布、联合恢复概率及素数传递仍未完成；
独立专项源码复核与最终文档头 CI 是合并前剩余门禁。

## 2026-09-30 07:16 UTC：无条件 RUN 精确验证及最新主线组合

无条件代码 `69c48f9e74426ef8004a761752c59d524f2d7fdb` 的
[push 36679099690](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679099690) 与
[PR 36679105586](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36679105586)
全部成功。实际日志中 `MaynardBFT.consecutive_primes`、
`OmegaBalance.bftbPrimeIndexRuns_unconditional`、
`OmegaBalance.f3PrimeIndexRunStarts_infinite_unconditional` 均仅依赖
`propext`、`Classical.choice`、`Quot.sound`。完整产生器、项目构建、内核回归、
650 个依赖模块源码/固定版本检查、99 个项目文件、646+1 精确审计和144240有限检查通过。

最终接口是：每个 L≥1 存在仅依赖 L 的自然数 C，对每个非零整数 c，
全体素数枚举 `Nat.nth Nat.Prime` 中有无限多个起始下标 r，使连续 L 个素数
的 F₃ 全为 c，且末首素数之差≤`f3RunModulus c * C`。长度1保留零跨度情形。
`F3PrimeIndexRunAt` 明确使用全体素数，不是某个筛选子列；原条件接口由实际
上游定理产生，不再作为未经证明的前提。

新增五条声明：`bftbPrimeIndexRuns_unconditional`、
`f3PrimeIndexRunStarts_infinite_unconditional`（F3BFTBMaynardAdapter），以及
`bftb_eventually_log_rpow_le_rpow`、`bftb_eventually_rpow_le_half_rpow_div_rpow_log`、
`bftb_eventually_floor_rpow_le_floor_half_rpow_div_rpow_log`（F3BFTBCutoff）。
原始固定 Lean/mathlib、真实参数边界和全部审计门禁保持不变。第三方来源说明
继续如实标注作者代码许可范围尚未确认；不把署名或沉默解释为许可。

随后真实三方合入已验 Haar 主线 `f45cd8a7586609555e8f307d25c38fee5c105249`，
保留双方全部数学源码字节及文档。组合候选是684条项目声明+1必需上游产生器、
105个项目文件；本地15项兼容测试、6项审计规则测试与源码/覆盖检查通过。
这个新增组合树仍须自己的完整 CI，不能用69c48f9的旧run替代。

原五项目标中的 INF/COR/DEN/LOG 已在主线；RUN 已有无条件内核证明，等待最新
组合验证与合并。全部接收 proof 任务尚未完成：全局 PAT、REC 等剩余概率/等待律、
其它登记节点继续开放。单次 Haar 范围已合入 PR51，不扩张为完整 REC 完成。


## 2026-09-30 REC-L6 finite-batch target-first reuse gate

Decision: implement the smallest genuine fixed-root finite-batch consequence
of the already proved actual Haar law, under `Measure.pi (fun _ : Fin T =>
f3UnitHaar)`. Target: REC theorem 2.3 / (2.7), with actual unit roots and finite
actual distance L≥1. T=0 is included. This is not a geometric PMF declaration,
infinite waiting-time theorem, expectation, or prime-sampling result.

The bounded target-first research was completed before implementation and its
full report was read. Searches included public web / mathlib GitHub queries
`firstSuccess geometric`, `firstSuccess`, `geometric hitting`,
`f3UnitHaar_rootDepth_ne`, and `certificate waiting`, before selecting the
finite-product and complement primitives. Then `infinitePi`, `hittingAfter`,
`integral_eq_tsum`, `lintegral_eq_tsum_measure`, `measure_biUnion_finset_le` and
`tsum_geometric ENNReal` were checked for the later boundary. No equal final
F3 theorem or first-success-from-independent-samples theorem was found in
that searched scope; this is bounded negative evidence, not universal absence.

Consumer remains Lean v4.34.0 / mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The current default-branch search
snapshot was `380f2aafb622cb2c1c93dac545b6389083c68c51`; decisions below were
rechecked at the consumer pin, including actual source signatures/proofs.

| Reused exact source | Locked blob / API and decision |
|---|---|
| [Constructions/Pi.lean](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Constructions/Pi.lean#L289-L317) | `2a62c773222f631197270b3ac84ea3efaf728458`; `Measure.pi_pi`, probability/SigmaFinite instances. Box mass is the finite product, no measurable-side premise needed for pi_pi |
| [Probability.lean](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean#L146-L156) | `854e28ccdb1cca99e61f76fceaad6390c1d227be`; `prob_compl_eq_one_sub`, applied to the proved measurable unequal event |
| [MeasurableSpace/Constructions.lean](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean#L708-L722) | `b66e9602adfff1ac1f45d9adf1ce804335ebc8f3`; `MeasurableSet.univ_pi` |
| [Data/List/FinRange.lean](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/List/FinRange.lean) | `61e2e0702872f77229101756e7daa20cdaa62e8f`; existing `List.finRange` / `List.mem_finRange` enumeration, not a replacement search algorithm |
| Existing project `F3RootDepthLaw.lean` | `rootDepth_ne_iff_mem_tail_union`, tail measurability, actual `f3UnitHaar_rootDepth_ne`; no probability premise replaces this proof |
| Existing project `F3RootReconstruction.lean`, `F3SharedRootHaar.lean` | `depthCertificateScan_eq_none_iff`, exact `f3SharedRootUnit_coe` and genuine-unit facts; existing algorithm and actual roots are retained |

The earlier source comparison found current finite-product blob
`13f98ef6a0bfe4c2c0eff540803351fb027f146a` retains the relevant API, and the
probability-typeclass source is byte-identical at the blob above. No upgrade
or backport is needed. All newly imported mathlib source headers are
Apache-2.0; imports copy no source and add no dependency or license terms.
The already accepted CC0 Haar port remains the existing dependency, not a
new port. The unrelated RUN author's unconfirmed license scope is unchanged.

The new module imports only existing F3SharedRootHaar/F3RootReconstruction,
finite `MeasureTheory.Constructions.Pi`, and `Data.List.FinRange`. It does
not add Probability.ProductMeasure, Independence.Basic, Geometric, or
HittingTime. Infinite-product first hit and its one-based indexing/expectation
need separate proofs. The exact unordered-pair union bound is deferred rather
than silently assuming pair independence or double-counting ordered pairs.

Ten project theorems are added once each to Audit. Local source/API, coverage
and finite checks are not Lean execution; the whole new candidate remains
pending exact locked-pin CI. [Scope and declarations](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30-rec-l6-fixed-root-finite-batch-candidate).

## 2026-09-30 08:17 UTC：固定根有限批次概率已通过精确 CI

代码 `c863b99d1ba71c4a63e9b555e36bb457e0918bef` 的
[push 36684973082](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36684973082) 与
[PR 36685062948](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36685062948)
全部通过。实际公理日志为695项（694条项目声明+1条必需上游产生器），仅标准三公理；
106个项目源文件、650个依赖源码/固定版本检查、一对一覆盖、内核回归、
144240有限检查均成功。独立专项源码/数学复核确认实际归一化 Haar、真实有限乘积、
共享单次参数、T=0及既有扫描接口，没有循环概率假设。

本节只升级 `F3RootBatchHaar.lean` 已列出的10条声明，得到固定实际单位根的
有限批次失败/扫描未知概率 `(1-3^(-L))^T`。原始完整配置的固定模型包装保留全部
前提和无限根点；未构造无限单边等待变量、未证明其均值、移动随机配置、
多对联合恢复界或素数传递。此前 candidate/pending 文字是实现历史。
最终文档提交仍单独执行完整CI，原始 proof 来源水位不因本次实现而改变。

## 2026-09-30: actual one-based waiting-time target-first reuse

Observed 2026-09-30 08:07 UTC. Read-only research, no new Lean execution or proof claim.
This continues the preceding fixed-root finite-batch reuse decision in this ledger.
Consumer pins: Lean v4.34.0, mathlib 5ed2965256430c3649e86755f9576b54eca72435.

### Target and decision

For fixed genuine p-adic unit roots with finite true distance L>=1, use the actual
infinite product Measure.infinitePi (fun _ : Nat => f3UnitHaar). One time coordinate
is one complete sample d shared by all root labels. Reuse MeasureTheory.hittingAfter
on the actual unequal-depth event, starting at0; define the paper's one-based waiting
time as hittingAfter +1 in ENat=WithTop Nat. Top remains top if no certificate occurs.

Prove the actual tail event equivalence before computing its mass. Then prove a
pointwise tail-indicator representation of this actual waiting variable, interchange
nonnegative sums/integral using existing mathlib, and evaluate the geometric series.
This is not a stipulated geometric PMF or a random variable named by its desired law.
The fixed-configuration scope remains explicit; moving random configurations, joint
recovery bounds and prime transfer are separate.

### Bounded search evidence

Existing report already searched firstSuccess/geometric/hitting and read Geometric.lean.
Additional actual GitHub code queries: integral nat tsum measure; lintegral enat;
hittingAfter expectation; lintegral_eq_tsum_measure; tsum measure natCast;
ENat toENNReal tsum; hittingAfter geometric; toENNReal tsum; lintegral tail;
tsum measure Ioi; ENat indicator; encard_Iio; tsum_ite_lt; lintegral_eq_tsum;
measurable_enat; ENat.toENNReal; toENNReal_natCast; toENNReal_add;
lintegral_tsum; ENNReal.sub_sub_cancel; lintegral_ne_top ae_lt_top; ae_lt_top;
tsum_eq_sum. GitHub PR searches: geometric hitting; expectation tail sum.
No equivalent final first-certificate mean theorem was found in this bounded scope.
Several search results were unrelated; they are not reuse candidates or absence proof.
The current default mathlib head was independently fetched as728a93eeff833da3173895bb0575752fdc24edb0.
Every recommended declaration below was separately read at the consumer pin.
Previously observed default head380f2a... is not substituted for current evidence.

### Exact pinned API map

All paths below are relative to:
https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/

1. Mathlib/Probability/Process/HittingTime.lean
- Lines65–68: MeasureTheory.hittingAfter (u : iota -> Omega -> beta) (s : Set beta)
  (n : iota) : Omega -> WithTop iota is the infimum of actual hit indices if one
  exists, else top. It is a genuine first-hit definition, not a distribution model.
- Line140: hittingAfter_eq_top_iff: hittingAfter u s n w = top iff every j>=n misses s.
- Lines238–248: hittingAfter_le_iff [WellFoundedLT iota]:
  hittingAfter u s n w <= i iff exists j in Set.Icc n i, u j w in s.
- Lines279–299: hittingAfter_lt_iff:
  hittingAfter u s n w < i iff exists j in Set.Ico n i, u j w in s.
The enclosing contexts supply the appropriate conditional complete order structure;
Nat has the needed instances. Read the actual context when implementing.
The current file differs from the pin, but these three exact declaration prefixes,
hypotheses and statements were checked unchanged. No upgrade is needed.

2. Mathlib/Data/ENat/Basic.lean
The source explicitly defines ENat / notation Nat-infinity as WithTop Nat.
ENat.some_eq_natCast is rfl; finite and top cases can use WithTop.recTopCoe.
The one-based shift must occur in ENat, not a toNat conversion that maps top to0.

3. Mathlib/Basic/Real/ENatENNReal.lean
- ENat.toENNReal_top, line50
- ENat.toENNReal_coe (n:Nat), line54
- ENat.toENNReal_eq_top/ne_top, lines65–66
- ENat.toENNReal_le/lt, lines69–73
- ENat.toENNReal_add, line94
- ENat.toENNReal_one, line98
These are the actual ENat-to-ENNReal coercion APIs for a nonnegative extended
expectation. Current default source is byte-identical to the pin.

4. Mathlib/Probability/ProductMeasure.lean
- Measure.infinitePi constructs the actual product of probability measures.
- IsProbabilityMeasure (infinitePi mu), lines378ff
- Measure.infinitePi_pi, lines402–411:
  for a finite index set s and measurable coordinate sets t_i,
  infinitePi mu (Set.pi s t) = product over i in s of mu_i(t_i).
Use s=Finset.range T and equal-depth event from the batch module. The sigma algebra,
probability instance and measure are actual constructions. Do not posit time
independence and then silently apply it to root labels.

5. Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean
- ENNReal.tsum_set_one, lines636–641: sum over x:s of1 equals s.encard as ENNReal.
- ENNReal.tsum_const_eq_top_of_ne_zero, line167
- General tsum_eq_sum is available to reduce a function supported on Finset.range N.
A minimal pointwise lemma specialized to the actual wait variable can split its
ENat value into finite N versus top and prove
  (tau(w):ENNReal) = sum'_T {indicator of T<tau(w)}.
For finite N, the support is range N and each term there is1. For top, every term
is1 and the sum is top. This small bridge was not found as an exact final library
theorem in the bounded search; it must actually be proved, not assumed.

6. Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean, lines354–359
Measurable.ennreal_tsum (h:forall i,Measurable(f i)) proves measurability of the
pointwise ENNReal series. It is deprecated in favor of Measurable.tsum from
Constructions/Polish/Basic but remains present at the pin. Avoid adding a larger
new framework merely to remove a nonblocking deprecation; alternatively use the
existing proof's iSup of finite measurable sums. No source copying is required.

7. Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean, lines362–370
lintegral_tsum [Countable beta] (hf:forall i,AEMeasurable(f i) mu):
  integral^- a, sum'_i f i a = sum'_i integral^- a, f i a.
Use measurable indicators of the already proved tail/cylinder events.

8. Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean, lines559–561
lintegral_indicator_one (hs:MeasurableSet s):
  integral^- a, s.indicator 1 a = mu s.
A generated lintegral_indicator_fun_one variant is also available.
This directly turns the actual pointwise tail-count identity into a probability sum.

9. Mathlib/Analysis/SpecificLimits/Basic.lean, lines403–412
ENNReal.tsum_geometric (r:ENNReal):
  sum'_n r^n = (1-r)^(-1), with no r<1 premise needed for this extended identity.
For p=(3^L)^(-1), the actual single-event probability implies p<=1.
Then ENNReal.sub_sub_cancel one_ne_top hp_le_one evaluates1-(1-p)=p,
and inv_inv gives the mean3^L. The exact ENNReal.sub_sub_cancel interface was
confirmed in its actual uses in pinned Probability.lean/Continuity.lean; fetch its
own defining source as needed before coding.

10. Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean, lines154–161
ae_lt_top' (hf:AEMeasurable f mu) (h2f:integral^- x,f x != top):
  almost everywhere f x < top.
ae_lt_top is the measurable variant.
Thus the finite proved expectation yields almost-sure finiteness without separately
rebuilding continuity-from-above or a Borel–Cantelli framework.
Current default source is byte-identical to the pin.

### Minimal implementation structure

A. Define actual stream measure, actual success set, and one-based hittingAfter+1.
B. Prove tau>T iff every n<T has equal depths; include T=0. Use hittingAfter_lt_iff,
   ENat addition arithmetic and the original unequal event, not a PMF law.
C. Prove finite-prefix event measurable; use coordinate evaluation and finite/countable
   intersections, or a finite Set.pi cylinder.
D. Apply infinitePi_pi and the existing actual equal-depth Haar mass to obtain the tail.
E. Prove the pointwise ENat tail-indicator identity, then measurability/lintegral exchange.
F. Evaluate the geometric series to the finite value3^L; derive almost-sure finiteness.
G. Add fixed original F3SharedRootConfig wrappers with all existing model assumptions.
Exact first-success point masses can follow from consecutive tails if useful, but are
not necessary to establish the paper's tail and mean. Do not mark all REC complete.

### Trust and status

All fetched mathematical library files carry the Apache-2.0 header. This route only
calls the existing locked dependency and copies no external proof corpus. Its hypotheses
are actual roots, actual finite distance and actual canonical sampling measure.
The listed candidate proof structure is not Lean-compiled. Every new declaration must
enter scripts/Audit.lean and the exact source tree must pass full project/producer,
regression, axiom, source and coverage CI before status promotion.

## 2026-09-30: F3-WAV-1-PROOF-BOUND target-first reuse gate

Target before implementation: for integer `h`, natural `r >= 2`, and the unchanged
strict window `2 < h < (3 : Int)^(2*r-1)-2`, prove
`¬ (3 : Int)^(2*r-1) ∣ h^2-4`. This is only the nondivisibility step in the
accepted WAV1 paper proof, not conditional transfer or a wavelet theorem.

Bounded searches performed before writing Lean on 2026-09-30:

- Web: `Lean mathlib wavelet discriminant h^2 - 4 prime power nondivisibility`,
  `"F3-WAV" Lean`, `site:github.com/leanprover-community/mathlib4 "h ^ 2 - 4"`,
  and `site:github.com "Lean" "discriminant" "nondivisibility"`
- GitHub code search of mathlib4: `wavelet discriminant` returned no entries;
  the final-form web queries surfaced unrelated discriminant material, not an
  identified equivalent final theorem in the inspected results
- Lemma-level web/GitHub queries for `pow_dvd_of_dvd_mul_left` and
  `pow_dvd_of_dvd_mul_right` identified the existing prime-power product API
- Decision: compose the locked mathlib prime and integer divisibility APIs in a
  small project-specific adapter. These bounded results do not establish that
  no equivalent proof exists anywhere, and do not justify new foundations

The exact APIs were read at the existing mathlib pin
`5ed2965256430c3649e86755f9576b54eca72435`, not inferred from current master:

- [Prime.pow_dvd_of_dvd_mul_left/right](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Algebra/Prime/Lemmas.lean#L94-L109),
  blob `70beb3f1460d26ac03d12d4f0cc65809c18b50b6`: a prime power dividing
  `a*b` divides the other factor when the prime does not divide one factor
- [Int.prime_three](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Nat/Prime/Int.lean#L63-L64),
  blob `e3c787bcbef6024c0d29c750be0f8266db1c172a`
- [Integer positive-divisor order interface](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Int/Init.lean#L318-L319),
  blob `fb55fc31647617a5556331fdc54dcbae5facd9a7`, explicitly using core
  `Int.le_of_dvd` with positive dividend and divisibility
- [Apache-2.0 license](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/LICENSE),
  blob `8dada3edaf50dbc082c9a125058f25def75e625a`, checked at the same pin

No external proof is copied; no dependency or toolchain change is needed.
Lean remains 4.34.0. Factor `h^2-4=(h-2)*(h+2)`; their difference is 4, so
3 cannot divide both. The API forces the entire power into one positive factor
strictly below that power, contradicting `Int.le_of_dvd`. No gcd or valuation
foundation is recreated. No local Lean/Lake executable is available; source
compatibility is not kernel verification, and exact-head CI remains required.

## 2026-09-30 08:30 UTC：WAV 精确 API 修复与当前主线组合

首个实际 PR run36686787116 在 F3WaveletLocal 第30行报告未找到未限定的
`dvd_sub`；并未通过内核门禁。源码已仅改为固定 Lean4.34 的 `Int.dvd_sub`，
其精确声明位于 src/Init/Data/Int/DivMod/Lemmas.lean:54–55，
blob99da2d83e13e782fb6ab3304b39321ded95e3737。公开命题、窗口及其余证明保持原样。
同时真实三方接入已验批次主线33ccdfe，保留全部10条新 Haar 批次声明和现有文档；
组合候选为699条项目声明+1条必需上游产生器，107个源文件。
新组合仍需精确CI，不能把源码/覆盖通过或旧基础CI当作WAV内核证明。

## 2026-09-30 09:03 UTC：WAV 短窗口修复已通过精确内核验证

代码 `c7e5d7d55209e575cc1449cf4595762f63469cf2` 的
[push 36690453078](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690453078) 与
[PR 36690460110](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36690460110)
全部成功：700项公理审计（699条项目声明+1必需产生器）仅含标准公理，
107个项目源文件、650个依赖模块及固定版本检查、完整覆盖、构建和回归均通过。
一般非整除引理与四个边界回归均有实际公理输出；独立数学/源码复核通过。

只升级 `F3-WAV-1-PROOF-BOUND`：严格窗口的整数判别式非整除、r=2/h=10旧大小界
反例及其正确结论、h=2零判别式、h=25排除端点的精确整除层/权重回归。
不宣告整个条件传递或WAV2–6已形式化，不把源PAPER-AUDITED归属解释为本次全包再审计。
首轮未限定dvd_sub的失败已据固定Lean4.34 API改为Int.dvd_sub，公开命题没有改变。

最终树另合入已验缓存工作流主线ef68dc4，数学源码与上述已验版本字节相同；
仅更换缓存保存范围，所有内核/源码/公理门禁保留。这个组合/文档头仍单独执行CI。

## 2026-09-30 09:40 UTC：实际固定根等待律已通过完整内核验证

代码0255c6b55f44ecb2fc7ee69a376969f655ac4e83，树3430edd9b9f09b4663e6018c8ec07a72b8c1d07e，
[push36697262997](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697262997)和
[PR36697267202](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36697267202)
均完整成功。12条新声明分别输出仅propext、Classical.choice、Quot.sound；全部712项
公理输出（711项目+1必需产生器）、108项目源文件、650依赖模块、固定版本、构建、
内核回归、一对一覆盖及144240有限检查通过。独立数学/源码复核和主线保留复核通过。

新增证明对应REC-L6/定理2.3式(2.7)的固定根及固定原配置部分：真实无限单位Haar流上，
一基首次证书时间（从不命中仍为∞）满足实际几何尾律，非负期望3^L，并且几乎处处有限。
逐点尾计数包括∞，没有用预设概率质量替换采样空间。实际原配置保留共同正基深度、
m≥2、互异同模3单位根；截断/联合矩阵停止界、移动配置、有符号差律和素数传递仍未完成。

前三轮编译失败属于类型包装/命名/API匹配：最终使用ENat专用递归、显式类型及
库hittingAfter等价的直接命题组合，避免重写器展开p-adic包装。没有改动公开结论或
前提，也未增加透明度/安全设置。以上是已验代码；本次状态文档头仍另行运行完整CI。

## 2026-09-30：REC-L7 实际联合停止尾界复用门

目标优先检索于09:49 UTC完成，消费基线PR54合入
`338442744c906dae107b65e83f010f0b76d71ad2`。先查最终最大几何等待/矩阵恢复尾界，
再查 `maximum geometric expectation tail bound`、`max geometric`、`coupon collector`、
`union bound exponential`、`tsum min exp`，及下述精确库符号。在已查范围未发现能直接
替代本项目真实根观测停止时间的最终定理；这不是一般不存在声明。均值所需分析留作下一批，
不先搭建新概率框架。

固定mathlib仍为 `5ed2965256430c3649e86755f9576b54eca72435`，Lean仍为4.34.0。
实施时重新直接读取锁定源码声明，而不只依赖研究报告。全部复用均为调用原库API，
不复制外部证明语料；源码Apache-2.0。查询当前上游 `f58d2cce48bddea8dacaa277791d40138cddc6fb`
仅作兼容检索；本项目不升版本，实际构建须使用固定pin。

| 锁定源码/声明 | 精确用途与边界 |
|---|---|
| [Finset/Prod](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Finset/Prod.lean)，blob `3a331ec6ea39157f7cb3c2725091d2ef94340233`；`Finset.card_product_filter_lt` | 直接给出规范i<j对的choose-two系数，不重做双计数 |
| [Finset/Lattice/Fold](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Finset/Lattice/Fold.lean)，blob `783cde945127918c9131e63274d5e39f464e61c2`；`sup_le_iff`、`lt_sup_iff`、`le_sup` | 自然数真实最大K与ENat真实最大等待；无限值保留 |
| [Measure/Real](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Measure/Real.lean)，blob `2be899626f4e667ab2434919350e73a0074fc0e8`；`measureReal_biUnion_finset_le` | 真实尾事件有限并上界，无根对独立或不交前提 |
| [Probability](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean)，blob `854e28ccdb1cca99e61f76fceaad6390c1d227be`；`measureReal_le_one` | 实际概率≤1，与指数包络合成min |
| [ENNReal/Operations](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Basic/ENNReal/Operations.lean)，blob `1006cb4b9e785650269a0d1c9aaf61c67d63b740`；`toReal_sub_of_le`，加既有`toReal_pow`/`toReal_inv` | 从已经证明的实际单对ENNReal律转换；先由真实成功概率证明p≤1，避免错误实化截断减法 |
| [Complex/Exponential](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Analysis/Complex/Exponential.lean)，blob `33157375f0b14cae92abf333dadef21ebbfce756`；`one_sub_le_exp_neg`、`exp_nat_mul` | 实数指数包络；不新建ENNReal指数体系 |
| [GroupWithZero/Basic](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Algebra/Order/GroupWithZero/Basic.lean)，blob `335ef50464487b5763d4ad885d55d83b00964f1b`；`pow_le_pow_left₀`、`pow_le_pow_right₀`、`one_le_pow₀`、`inv_le_inv₀`、`inv_le_one_of_one_le₀` | 非负幂及反比例比较，保留所需正性 |

本项目已有 `f3SharedRootWait`、原配置等待尾律、`rootDepth_eq_valuation` 和
`depthCertificateScan_recover_iff` / `depthCertificateMatrix_recover` 直接复用。
新增只是实际有限max/事件桥/union适配，14条候选声明全部进入Audit。
真实根距的toNat转换仅在互异且赋值≥1后通过Lean4.34 `Int.toNat_of_nonneg`证明正确，
不对∞或对角做这一转换。最新主线接口研究证据、静态源码检查、实际内核编译明确分开。
[精确映射及未覆盖部分](proofs/f3/prime_depth_reconstruction/formalization.md#2026-09-30rec-l7-实际全矩阵停止尾界候选)。

## 2026-09-30 10:12 UTC：REC-L7 实际联合停止尾界已通过精确 CI

代码0324861a6b94294421d692203e8847802b1044f4，树dbbe7e42a1c38aff722b05568ca5c9a957fe69dd，
[push36700614557](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700614557)和
[PR36700618251](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36700618251)
均完整成功。14条新声明逐条仅依赖propext、Classical.choice、Quot.sound；全726项
公理输出（725项目+1必需产生器）、109项目源文件、650依赖模块及固定版本、完整构建、
内核回归、覆盖和144240有限检查通过。

已验范围是REC-L7/定理2.3式(2.8)的尾界部分：固定原配置的真实一基最大等待时间，
按i<j恰计choose(m,2)对，K为这些实际有限根距的最大值；逐点证明τ≤T等价于原证书
矩阵恢复全部真实根距，保留∞对角线、命中根和T=0。真实单位Haar无限流的尾概率
不超过min(1,choose(m,2)·exp(-T·3^-K))，仅使用对之间并集界，不假设根对独立。

首轮编译失败已作四处语法/推断/存在量词归一化修复，14条公开命题及模型前提不变。
185653个有限批次（含27607个命中根批次）只是补充语义回归。对数期望界、移动配置、
完整有符号差律及素数传递仍开放，不把尾界当作这些结论。本次状态文档头还需独立完整CI。

# REC-L7 actual joint waiting mean: reuse gate

Observed 2026-09-30 10:32 UTC. Consumer master ee2888060c59be83720f77cc870868e9709ba170; Lean4.34.0, mathlib5ed2965256430c3649e86755f9576b54eca72435. The joint maximum, exact matrix stopping event and exponential tail are already kernel-verified. This report prepares the remaining actual expected-maximum bound, not a new probability model.

## Target and minimal route
For the fixed original F3SharedRootConfig, prove the nonnegative expectation of actual f3JointRootWait is at most ENNReal.ofReal(1+3^K*(1+Real.log(m.choose2))), with K the existing actual maximum root distance. Preserve infinite never-hit streams in ENat. C.two_le_card gives B=m.choose2>=1; p=(3^K)^(-1)>0. No independence across root pairs.

Use f(x)=min(1,B*exp(-p*x)). It is nonnegative, continuous and antitone. Dominate it by the integrable exponential on Ioi0. Split the integral at c=log(B)/p>=0; bound by 1 on Ioc0c and Bexp(-px) on Ioic. This only uses inequalities, avoiding a needless piecewise equality. Existing exponential integration gives c+1/p. The existing integral test bounds the real series by 1+(logB+1)/p. Use the existing actual joint tail bound, an actual ENat pointwise tail-count identity including infinity, lintegral_tsum, and ofReal_tsum_of_nonneg to transfer to the genuine waiting expectation. Do not use toNat on infinite waits or postulate a geometric PMF. Almost-sure finiteness may follow from the finite bound, but is not a substitute for the exact mean inequality.

## Bounded target-first search
Existing joint-tail report searched maximum geometric expectation tail bound, max geometric, coupon collector, union bound exponential and tsum min exp. This continuation queried GitHub mathlib4 code for geometric maximum, tsum_le_integral, integral_exp_mul_Ioi, integral_Ioi integral_Ioc, Integrable.mono AEMeasurable, ofReal_tsum, integral_const Ioc, volume_real_Ioc, integrableOn_const and choose_pos. No equivalent final actual matrix-wait mean theorem was found among the inspected results; this is bounded negative evidence, not a universal absence claim.

## Exact pinned API signatures
All paths below are relative to https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/ . Read surrounding typeclass contexts; in particular setIntegral_mono_on has explicit preceding hf:IntegrableOn f s mu and hg:IntegrableOn g s mu arguments.

Mathlib/Analysis/SumIntegralComparisons.lean
theorem AntitoneOn.tsum_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑' (n : ℕ),  f n ≤ f 0 + ∫ x in Ioi 0, f x

Mathlib/Analysis/SumIntegralComparisons.lean
theorem AntitoneOn.summable_of_integrableOn_Ioi_zero (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    Summable (fun (n : ℕ) ↦ f n)

Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean
theorem integrableOn_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Ioi c)

Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean
theorem integral_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Real.exp (a * x) = - Real.exp (a * c) / a

Mathlib/MeasureTheory/Integral/Bochner/Set.lean
theorem setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ

Mathlib/MeasureTheory/Integral/Bochner/Set.lean
theorem setIntegral_mono_on (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ

Mathlib/MeasureTheory/Integral/Bochner/Set.lean
theorem setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • c

Mathlib/MeasureTheory/Function/L1Space/Integrable.lean
theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ

Mathlib/MeasureTheory/Function/L1Space/Integrable.lean
theorem Integrable.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α → β}
    (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hnonneg : ∀ᵐ a ∂μ, 0 ≤ f a)
    (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    Integrable f μ

Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean
theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n)

Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean
theorem volume_real_Ioc_of_le {a b : ℝ} (hab : a ≤ b) : volume.real (Ioc a b) = b - a

Mathlib/Data/Nat/Choose/Basic.lean: Nat.choose_pos {n k} (h:k<=n):0<n.choose k.

Mathlib/MeasureTheory/Integral/IntegrableOn.lean:119: integrableOn_const {C} (hs:mu s != infinity := by finiteness) (hC:enorm C != infinity := by finiteness):IntegrableOn (fun _=>C) s mu. For real constants on finite Ioc, both side conditions hold.

Existing verified F3RootWaitingHaar already uses lintegral_tsum, lintegral_indicator_fun_one, ENat.toENNReal coercions and ae_lt_top. Reuse the same actual tail-count pattern or a small generalized helper, with every project theorem registered exactly once in Audit. The one-step pair law and actual joint exponential tail remain existing conclusions, not hypotheses named after the final target.

## Version, source identity and license
The current search index resolved to 7b4f42a6b9014145e9b791f85d298656c3ef294d; that Git commit was independently fetched. Each relevant current source was fetched separately and its selected declaration signature compared with the consumer pin; all listed signatures are unchanged. Files can differ elsewhere. No upgrade recommended. All inspected source headers are Apache2 and the pinned LICENSE was fetched separately. No upstream corpus is copied; only existing pinned APIs are called.

Pinned/current Git blob SHA1 values computed from the fetched UTF8 Git blob bytes:

- Mathlib/Analysis/SumIntegralComparisons.lean: pin 2d4cb29ea8a78cbb61f9f1272d0afc24a9722a21; current 90456b6561257a9f25947cc1fa8b9cb5cd58d8c4

- Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean: pin e5944768a5833e19d8da7f7c5b7ad77e65fcfe0c; current 8571a78c8e7ce0079dc1f0ac5c06bd4888fd87f1

- Mathlib/MeasureTheory/Integral/Bochner/Set.lean: pin c2f23b4ffdeaafa6c1e4faf7407788f785400da8; current ec3b1499ef4042a604ef01ac4d1c180038984d3e

- Mathlib/MeasureTheory/Function/L1Space/Integrable.lean: pin 2ad180afca8fb23408d5408050a8965089375ae5; current 7c51bb765bfec75158a4ec4c859bd27bf1da996e

- Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean: pin dd73efd48dd32e4ef53e40ec6aa70f40ebde9830; current 0c568369df1f74282f0ec4cc40d38c33bc12012b

- Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean: pin 84794cf74fa34664073bbf336adccdefb5bada62; current a9e421ce29372e8cae9337a62fc4a02b583cda89

- Mathlib/MeasureTheory/Integral/IntegrableOn.lean: pin a61d29fe081da762dd3cd6a4a8b34f95740378c1; current 320145ba4c47542e99f835ca2998d69946420359

- Mathlib/Data/Nat/Choose/Basic.lean: pin 1cd090d71c8175e5f2071d939d30394b4c56d9de; current 1cd090d71c8175e5f2071d939d30394b4c56d9de

## Acceptance boundary
This source review is not Lean compilation. The analytic envelope calculation, actual maximum tail-count/integral bridge, exact paper wrapper and every new declaration still require implementation, full exact-tree Actions kernel/axiom/source/coverage/regression verification and independent review. Moving configurations, signed difference laws, prime transfer and other accepted packages remain separate.

## 2026-09-30 10:47 UTC：REC-L7 实际联合等待对数期望已通过精确 CI

代码1b9a0d63b4c2be6d063dda68a60f1ceffa7cf130，树de59e407b238b301cafa9474a4babeb9cb553d58，
[push36704236926](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704236926)与
[PR36704245738](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36704245738)
完整成功。12条新声明仅标准公理；全738项公理输出（737项目+1产生器）、110项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查全部通过。

REC-L7/定理2.3式(2.8)的实际最大等待时间满足原精确上界
Eτ≤1+3^K(1+log choose(m,2))，这里期望是保留∞的真实非负积分，K为实际根距最大值。
已证明真实最大等待几乎处处有限，原有证书矩阵几乎处处在某个有限T恢复全部真实距离。
证明调用锁定库的指数积分/积分判别和已验真实联合尾界；没有预设分布或根对独立性。

首轮编译的默认有限区间质量、反单调限制集参数、Nat索引/局部常量展开及符号归一化
已显式修复，12个公开命题及全部前提保持不变。294个浮点解析前缀与28个有限样本尾和
仅为补充回归。显式置信参数δ推论、移动配置、完整有符号差律和素数传递仍开放。
本次状态文档头保留全部已验代码和审计，仍独立执行完整CI。原纸面来源水位不变。

# REC-L7 explicit confidence corollary: reuse gate

Observed 2026-09-30 10:53 UTC. Read-only target-first preparation; no code or kernel claim. Consumer Lean4.34.0/mathlib5ed2965256430c3649e86755f9576b54eca72435. Existing F3JointWaitingHaar proves the actual finite-pair maximum tail with exact choose-two coefficient and actual K; F3JointWaitingMean proves tail measurability on the same actual stream.

## Target
For a fixed original F3SharedRootConfig, 0<delta<1 and natural T satisfying T>=3^K*log((m.choose2)/delta), prove the real probability of actual complete certificate-matrix recovery after exactly the firstT whole observations is at least1-delta. Preserve actual matrix equality, genuine shared stream, true infinite diagonal/root-hit depths, actual K and all C hypotheses.

## Bounded search and decision
GitHub final-target queries log confidence and exp_neg log measureReal found unrelated weak-topology, tilted-measure and moment/subGaussian results among inspected matches, not an equivalent final matrix-certificate confidence theorem. Exact API query measureReal_compl identifies the minimal finite-probability complement bridge. Bounded only, not an absence proof. Reuse the already-proved project tail and matrix iff plus elementary locked log/exponential and complement APIs; no new dependency or probability framework.

## Exact APIs
All paths relative to https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/ .

- Mathlib/MeasureTheory/Measure/Real.lean:409, blob2be899626f4e667ab2434919350e73a0074fc0e8:
MeasureTheory.measureReal_compl [IsFiniteMeasure mu] (hs:MeasurableSet s): mu.real s.compl=mu.real univ-mu.real s.
It requires the actual measurable failure event and finite measure. Existing stream probability and joint-tail measurability supply these; real mass of univ is1.
- Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:59, blob0ed3c957d0d1f37094a8da10e42e6d2c2807e7be:
Real.exp_log {x:Real} (hx:0<x):exp(log x)=x.
Use positive B/delta, not log at zero. Real.exp_neg and Real.exp_le_exp are already directly used and kernel-verified in preceding consumer modules at this pin.
- Existing Nat.choose_pos C.two_le_card proves B=m.choose2>0. Positive3^K permits division. Ordered-field arithmetic turns T>=A*log(B/delta) into exp(-T/A)<=exp(-log(B/delta)); multiplication by B gives <=delta exactly.
- Derive actual success as the complement of the failure event pointwise from f3JointRootWait_le_iff_matrix_recover; do not assume this correspondence or root-pair independence.

## Current and license comparison
Current search index resolved to dca97ab984e97c9d1edcdbea3dc9e0c0c1d673ee, independently fetched as a commit. Current Measure/Real blob91ebdd41fdbc3f448c4f4120e19a9b774696c567 and Log/Basic blob9a7df2d42999a58e7619e89227ba5e75d6ba60a6 were separately read. Selected signatures/hypotheses unchanged. No upgrade proposed. Both source headers declare Apache2; pinned root LICENSE directly checked in this integration round. Only library calls/project adapters planned, no external proof corpus copied.

The corollary still requires implementation and full exact CI. Moving configurations, prime transfer, signed differences and other accepted results remain open.

## 2026-09-30 11:04 UTC：实际完整矩阵置信保证已通过精确 CI

代码361cdd3c958897b342297dfbc7abb55a66e3a4cb，树6979590446d56975243dd667081e37c40542456f，
[push36705872257](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705872257)和
[PR36705919682](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36705919682)
首轮完整成功。三条新声明仅标准公理；全741项公理输出（740项目+1产生器）、111项目
源文件、650依赖模块及版本锁、构建、内核回归、覆盖和144240有限检查全部通过。

对原固定配置、0<δ<1和自然T≥3^K log(choose(m,2)/δ)，真实单位Haar流前T次观测使
原证书矩阵恢复全部真实距离的概率至少1−δ。成功事件通过已有逐点矩阵等价和可测尾
补事件证明，不预设目标概率；K为实际根距最大值，根命中∞及真实∞对角线保留。

与先前已验标量尾律/期望、联合尾界/对数期望一起，覆盖纸面定理2.3在固定原局部模型
中的式(2.7)、式(2.8)及其显式置信推论。整个REC包仍未完成：截断概率、移动配置、
全素数传递、有符号差律、被动下界和三等距根精确停止律等继续开放。36个数值阈值与
8个有限根模型有理成功概率仅为回归。独立数学/源码复核通过；此状态文档头仍另行
执行完整CI。原始proof来源水位保持不变。

# REC-L12 truncated single-certificate Haar law: reuse gate

Observed 2026-09-30 11:09 UTC. Consumer master3b0d3aad1665b47dc1a169fd8111ccb74ce7df99, Lean4.34.0/mathlib5ed2965256430c3649e86755f9576b54eca72435. Accepted paper proof theorem2.6 equation(2.13), not its yet-unproved finite-batch matrix bound or prime transfer.

## Target and actual domain
For positive natural precision H (the existing representation of the paper's positive integer precision), genuine unit roots with finite true distance L>=1, observe min(rootDepth,H). Use the existing truncatedDepthWitness: unequal observations OR both saturated at H. Prove its actual normalized unit-Haar probability is3^(-L) if L<H, and1/(2*3^(H-1)) if H<=L. Preserve root-hit infinity before truncation. The cutoff acts on normalized R, not raw D=b+R. A wrapper must use the original F3SharedRootConfig and its proved actual off-diagonal exponent, not assume a probability law.

## Bounded final-target search
GitHub mathlib4 code queries truncated padic; valuation certificate; min_eq_min; min_eq_iff. Final-target searches returned unrelated Witt-vector/tactic material among inspected results, not an equivalent actual truncated-certificate probability theorem. This is bounded evidence only. The minimal route reuses the existing project ultrametric/certificate and exact Haar tail/unequal laws; no probability or valuation foundations are rebuilt.

## Exact project reuse at consumer master
- OmegaBalance/F3RootCertificates.lean blob4ebd2866950885848efca01b5157f7e4941a59bf:
  rootDepth_min_le_distance d a b; rootDepth_min_eq_distance_of_ne (unequal actual extended depths);
  truncatedRootDepth_ne_certificate: unequal truncated depths imply true rootDistance equals their minimum and that minimum<H;
  truncatedRootDepth_saturated_certificate: both cut depths=H imply H<=rootDistance and true truncated target=H.
  Existing definitions use WithTop Int and retain infinity.
- OmegaBalance/F3RootTruncatedReconstruction.lean blob4a24db55453664e08976cd883757912c874f1adb:
  truncatedDepthWitness, truncatedDepthCertificate_eq_some_iff and the actual finite scan/matrix. Keep this algorithm and success event.
- OmegaBalance/F3RootDepthHaar.lean blob7c41520fbd70c7001d2096f0822bc60188ed7ab6:
  f3RootDepthTail a H is the actual threshold event, measurable;
  f3UnitHaar_rootDepth_ge (ha:IsUnit a) (hH:1<=H) gives its actual mass (2*3^(H-1))^(-1).
- OmegaBalance/F3RootDepthLaw.lean blob0e014a2a754b6635a999b4473587cba84b447310:
  f3UnitHaar_rootDepth_ne (ha:IsUnit a)(hb:IsUnit b)(hLpos:1<=L)(hL:actual distance=cast L) gives actual unequal-depth mass (3^L)^(-1).
- OmegaBalance/F3RootBatchHaar.lean blobb3862170beda67dd0d0bfd00698ad7c311c94c5d:
  f3RootDepth_ne_measurable hL gives measurability of the actual unequal event.
- Existing f3RootDistanceExponent_eq/pos on original C supplies actual finite positive distance for distinct labels. It is already kernel verified; no new rational-only model.

## Minimal mathematical composition
When L<H, joint saturation is impossible by the existing saturated certificate. A raw unequal pair has minimum=L<H, so truncation preserves a strict inequality; conversely unequal cuts imply unequal raw depths. Thus success event is exactly the already-proved unequal event.
When H<=L, unequal cuts are impossible by the existing unequal certificate. Saturation of the first root also saturates the second by the ultrametric minimum bound and valuation subtraction symmetry. Thus success is exactly the first root's H-tail.
Uniform lower bound is even simpler: the H-tail of the first root is always a subset of the success event, regardless of root distance; if the second cut is not H the cuts differ, otherwise both saturate. Measure monotonicity supplies the bound without rebuilding ENNReal inverse inequalities.
Only the single-observation law, its measurability, uniform lower bound and fixed-C wrappers are the first implementation slice. Finite-batch matrix recovery probability and all-prime transfer remain open.

## Locked external API/current/license check
Mathlib/Order/MinMax.lean at5ed2965, blobde014275ed509bebd700df981e9562e26194bbe7:
- line79 min_eq_right_iff: min a b=b iff b<=a
- line97 min_lt_min_left_iff: min a c<min b c iff a<b and a<c
Used with the linear order WithTop Int. The currently indexed commit0e51f706a3f127b7a708185c0bd7b4beb74d5a17 was separately fetched; current file has the identical blob and declarations. Header Apache2, pinned root LICENSE checked in this round. AddValuation.map_sub_swap was already read at the fixed pin and used in the verified project. No new dependency, toolchain upgrade or external proof copying.

## Intake refresh and acceptance
At11:09 UTC, git fetch listed172 actual remote heads (excluding origin/HEAD). Compared155 original watermark entries: only master moved; original research heads are unchanged. Repository issues updated since09:11 were only this integration's PR53/54/56/57/58. No additional external mathematical package found; do not alter original source watermarks. Every new lemma needs Audit exactly once and full exact-tree Actions plus independent review. This report is not kernel verification.

## 2026-09-30 11:23 UTC：单次截断证书 Haar 分段律已通过精确 CI

代码94bc0693b5c1bfca7d054d20daf9efea00a0b67a，树9ba2bea3889e77d85a63fcf3c86d3f27b51d0250，
[push36707863669](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707863669)与
[PR36707908267](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36707908267)
首轮完整成功。12条新声明仅标准公理；全753项公理输出（752项目+1产生器）、112项目
源文件、650依赖模块及版本锁、构建、内核回归、精确覆盖和144240有限检查通过。

已覆盖REC-L12/定理2.6式(2.13)的实际单次概率：L<H时证书事件等于原不等深度事件，
质量3^(−L)；L≥H时等于真实共同H球，质量1/(2·3^(H−1))，包括L=H。另有可测性、
实际事件包含给出的统一下界、原固定配置包装。H截断标准化R，命中根∞保留至截断，
恢复目标仍为min(L,H)。高距离一般引理允许更广根域，但最终包装保持原C全部前提。

30个精确有限剩余类案例6564次观测含60次根命中只是补充回归；H=0反例说明为何质量
公式要求H≥1。独立源码/数学复核通过。式(2.14)的有限批次截断矩阵尾界、移动配置、
全素数传递与整个REC包仍开放。此状态文档头不变更已验代码或审计，仍单独执行完整CI。

# REC-L12 finite-batch truncated matrix tail: reuse gate

Observed2026-09-30 11:35 UTC. Consumer master07338ca65c689d8c9b8882744891a777b542efca; Lean4.34.0/mathlib5ed2965256430c3649e86755f9576b54eca72435. Actual single-observation truncated certificate law and uniform lower bound are integrated after complete kernel/audit CI. Target accepted proof theorem2.6 equation(2.14).

## Exact target/domain
For fixed original F3SharedRootConfig C, H>=1 and natural T, sample T complete parameters under the actual finite product Measure.pi(fun _ : Fin T=>f3UnitHaar). Each parameter is shared by all root labels. Bound the real probability that the existing truncatedDepthCertificateMatrix on List.finRange T is not the true matrix min(L_ij,H) by min(1,choose(m,2)*exp(-T/(2*3^(H-1)))). Include T=0, root hits/infinite raw depths, diagonal H and joint saturation. Never replace unknown by a numerical distance or recover true distances aboveH. No independence across root pairs.

## Final-target search and minimal reuse
Bounded GitHub mathlib4 searches: truncated certificate returned0; pi_pi compl found the existing finite-product construction among unrelated files; measureReal_biUnion_finset_le identified the exact union bound. No equivalent final truncated matrix-recovery theorem found in inspected results. This is not a global absence claim.
Reuse the actual project certificate event and its measured positive lower bound, the existing deterministic truncated matrix recover iff, and canonical f3RootPairs/card from the full-matrix module. Do not rebuild independence or valuation theory.

The pair-failure event is the finite product rectangle of the complement of the actual single-success event. Thus its exact mass is mu(single-failure)^T. Convert once to real probability, use measured success>=q=1/(2*3^(H-1)), then the existing Real.one_sub_le_exp_neg/power identity to bound by exp(-Tq). Full matrix failure is exactly a finite union over i<j of these pair failures, using witness symmetry, fixed actual roots and the existing matrix recover iff. The finite-union bound requires no pair independence and cardinality is exactly m.choose2.

## Locked library source interfaces
Paths relative to https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/ .
- Mathlib/MeasureTheory/Constructions/Pi.lean:290, blob2a62c773222f631197270b3ac84ea3efaf728458:
  Measure.pi_pi [Fintype iota] [forall i,SigmaFinite(mu i)] (s:forall i,Set(alpha i)):
  Measure.pi mu (Set.pi Set.univ s)=product_i mu_i(s_i).
  Same file:307/311 supplies finite/probability instances for the finite product. Existing unit Haar is already a genuine probability measure. Empty Fin0 product gives mass1.
- Mathlib/MeasureTheory/Measure/Real.lean:146, blob2be899626f4e667ab2434919350e73a0074fc0e8:
  measureReal_biUnion_finset_le (s:Finset beta)(f:beta->Set alpha):
  mu.real (union b in s,f b)<=sum b in s,mu.real(f b).
  No disjointness or independence premise.
- Same file:409 measureReal_compl [IsFiniteMeasure mu] (hs:MeasurableSet s):
  mu.real(s.compl)=mu.real univ-mu.real s.
- Already inspected and kernel-used at this consumer pin: ENNReal.toReal_pow, toReal_mono, toReal_inv/toReal_mul; Real.one_sub_le_exp_neg; Real.exp_nat_mul; measureReal_le_one; MeasureTheory.MeasurableSet.univ_pi; Finset.card_product_filter_lt.
- Existing deterministic truncatedDepthCertificateMatrix_recover_iff uses actual root distances fixed across samples. Instantiate roots as C.root, hfixed by reflexivity; do not assume the desired output.
- Existing F3TruncatedCertificateHaar gives measurable success for actual finite distance and the uniform event-inclusion lower bound. The original C wrapper supplies true finite distances for distinct canonical pairs.

## Current compatibility and license
Current search index resolved to b9579600c1115f822b7bfc0afee4f454a82116ca, independently fetched as a Git commit. Current Pi blobfd0e501cf14e19104cfa989adf4625e84ce8c974 and Real blob91ebdd41fdbc3f448c4f4120e19a9b774696c567 were fetched separately. The selected pi_pi, finite-union and complement signatures/hypotheses were directly compared and unchanged. Source headers and pinned root license are Apache2. Only existing pinned APIs/project proofs are reused; no new dependency or copied proof corpus.

## Acceptance boundary
This is a pre-implementation reuse decision. New declarations must enter Audit exactly once and pass full exact-tree Actions plus independent review. No first-hit waiting variable or expectation is needed for the paper's finite-batch bound. Moving configurations, all-prime sampling/transfer, signed difference laws, passive bounds and triple stopping laws remain open.

## 2026-09-30 11:47 UTC：实际有限批次截断矩阵尾界已通过精确 CI

代码95c32fe0de79502fba19972d86d327c32103eaf6，树647521f257918a7625542896e07ef320a7dae25f，
[push36710285308](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710285308)与
[PR36710327735](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36710327735)
首轮完整成功。11条新声明仅标准公理（证书对称引理不依赖任何公理）；764项总输出
（763项目+1产生器）、113项目源文件、650依赖模块及版本锁、构建、内核回归、一对一
覆盖和144240有限检查通过。测试PR合并树与上述源码头的文件树相同。

已覆盖REC-L12/定理2.6式(2.14)：真实有限单位Haar乘积采样下，既有截断矩阵算法
未恢复min(L,H)的概率≤min(1,choose(m,2)·exp(−T/(2·3^(H−1))))。对角线H、联合饱和、
命中根原深度∞和T=0保留；时间乘积与根对并集分别证明，没有根对独立性假设。
连同已验单次式(2.13)，当前覆盖原固定模型的两条截断概率公式及实际算法事件。

84个有限案例45143批次（含16636根命中批次）只是补充回归。独立数学/源码复核
通过；有限精度不可辨识的完整分布声明、移动配置和全素数传递仍开放，不能把整个
定理2.6或REC包全部标成完成。此状态文档头不变更已验代码/审计，仍另行完整CI。

# Finite-precision two-output nonidentifiability: exact-law reuse gate

Observed2026-09-30 11:53–12:12 UTC. Consumer master50942b02105f6372da0d8d4d8629caf0da65188c, Lean4.34.0/mathlib5ed2965256430c3649e86755f9576b54eca72435. Target is the final local paragraph of REC proof theorem2.6: when both genuine root distances are at least H, the two-coordinate truncated observation laws agree, and so do the laws of every finite independent batch. This is stronger and more appropriate than equal moments.

## Actual domain and chosen minimal route
Use existing rootDepth : Q_3 -> Q_3 -> WithTop Int and truncatedRootDepth=min(rootDepth,H), retaining the infinite root value before truncation. Define only transparent observation functions of these existing statistics. Prove their measurability and compare their actual pushforward measures under f3UnitHaar.
The existing positive-depth tails are independent of the unit root, nonpositive tails are universal, and the top fiber is the proved null root singleton. Locked finite-measure uniqueness on Ici sets therefore gives equality of the entire raw single-root laws. Compose with the measurable min-at-H map to obtain the entire truncated marginal law.
When H<=rootDistance(a,b), the two truncated coordinates agree pointwise, including root hits. Factor the actual pair observation through the diagonal of its first marginal, then use the marginal pushforward equality. Finally apply the existing finite-product pushforward theorem to every T, including T=0. A fixed-original-model wrapper and an H-versus-strictly-higher-distance corollary preserve the paper's assumptions.
Every observation map is explicitly proved measurable before using map_apply/map_map/pi_map_pi. Do not rely on Measure.map's fallback for an unproved nonmeasurable map.

## Bounded final-target and API search
Queries included padic distribution; measurePreserving addHaar; IsHaarMeasure Equiv; continuous/measurable addValuation; continuous_valuation; Measure.ext singleton Countable; measurable_iff singleton Countable; map_pi Measure; map_map in MeasureTheory. No equivalent final censored two-root pushforward-law theorem was found in the inspected results; not a universal absence claim.
Current Mathlib/NumberTheory/Padics/Measure/Monoid.lean was inspected and rejected: it is AbstractMeasure D(G,R) convolution on topological monoids, not the actual real-valued normalized Haar observation law, and is absent at the consumer pin. No port or upgrade is justified. General Haar automorphism APIs were located, but the existing exact project tails plus the final measure-uniqueness interface are a smaller bridge and avoid rebuilding valuation/Haar foundations.

## Existing verified project inputs
At consumer master:
- F3RootDepthHaar.lean blob7c41520fbd70c7001d2096f0822bc60188ed7ab6: zero tail=univ; measurable actual tails; unit-root tail mass(2*3^(t-1))^-1 for t>=1.
- F3RootDepthNull.lean blob5a8370a224b0f6abf42b03d8a5b3eb02b8b4b381: every actual unit-Haar singleton is null; the infinite-depth event equals the actual root singleton, not a zero layer.
- F3RootCertificates/F3TruncatedCertificateHaar: unequal cuts force true distance<H; hence H<=distance gives pointwise equal cuts. Original C wrappers use the existing genuine integral-root representatives and their proven coercion identity.
These are conclusions already kernel-verified, not probability assumptions.

## Locked external interfaces
Paths relative to https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/ .
- MeasureTheory/Constructions/BorelSpace/WithTop.lean, blob9a13abed88439e018183388d1697e55b76c9437b: standard Borel measurable space on WithTop of a linearly ordered order-topological space; no custom sigma algebra.
- Topology/Order/WithTop.lean:34 gives SecondCountableTopology(WithTop iota) from the corresponding base instance. Int has the required order/Borel structure.
- MeasureTheory/Constructions/BorelSpace/Order.lean, blob373362a90f7b59d21ae884ceadb84fc51fcae514:
  measurable_of_Ici (hf:forall x,MeasurableSet(f^-1'Ici x)):Measurable f, under BorelSpace/LinearOrder/OrderTopology/SecondCountableTopology and a measurable domain.
  Measure.ext_of_Ici (mu nu:Measure alpha) [IsFiniteMeasure mu] (h:forall a,mu(Ici a)=nu(Ici a)):mu=nu, with explicitly listed Borel/order/second-countable hypotheses.
  Measurable.min gives the measurable cutoff map.
- MeasureTheory/Measure/Map.lean, blob767657b96b1f0b439934e230c9561ca0d343244e:
  Measure.map_apply (hf:Measurable f)(hs:MeasurableSet s):mu.map f s=mu(f^-1's).
  Measure.map_map (hg:Measurable g)(hf:Measurable f):(mu.map f).map g=mu.map(g o f).
- MeasureTheory/Constructions/Pi.lean, blob2a62c773222f631197270b3ac84ea3efaf728458:385:
  Measure.pi_map_pi, finite index, coordinate measurable spaces, [forall i,SigmaFinite((mu_i).map f_i)], and hf_i:AEMeasurable f_i mu_i:
  (Measure.pi mu).map(fun x i=>f_i(x_i))=Measure.pi(fun i=>(mu_i).map f_i).
  Actual probability measures and measurable observation maps supply these hypotheses. The same sample is fed to both coordinates at each time.

## Current compatibility/license
The current default mathlib master was independently fetched at12:12 as5bd58ac291422a21f412ae354c91e7d172255a2c. Selected current files were separately read; map and WithTop Borel files are byte-identical, while Order current blob0b605af332546cd8a0af932f2e9fd8d6f35ff6c6 and Pi current blobfd0e501cf14e19104cfa989adf4625e84ce8c974 differ elsewhere. Selected ext_of_Ici/measurable_of_Ici/pi_map_pi signatures are unchanged; required typeclass contexts were inspected. Apache2 source headers and pinned root license checked. No dependency upgrade or external proof corpus copying.

## Acceptance boundary
No new code or kernel proof is claimed by this report. All new declarations require Audit exactly once, full exact-tree Actions and independent review. Equality concerns observations alone under the original local Haar model; it does not deny recovery from separately supplied coefficients, nor assert equality of finite prime-box laws. Moving/prime sampling, signed differences, passive lower bounds, triple stopping and other accepted packages remain open.

## 2026-09-30 12:34 UTC：完整双输出截断观测分布已通过精确 CI

代码add478972bb5b3cd2a255cc0aab1ef6e078578b1，树7b38ee3b132fb3039518f4700ea3b4d509cdc44f，
[PR36715105909](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36715105909)
首轮完整成功；实际测试合并提交864ceb48a06109125d76756a0f41bd4161423530的文件树相同。
14条新增声明只有标准公理，778项总审计输出（777项目+1产生器）、114项目源文件、
650依赖模块及版本锁、构建、内核回归、一对一覆盖和144240有限检查均通过。

现已覆盖REC定理2.6的固定双根、有限精度完整观测分布不可辨识结论：标准单位Haar
采样下，两模型的真实根距均至少H时，每个有限T的完整双输出观测序列具有相同分布，
包括真实距离H与K>H的比较。原模型包装保留共同已知基深度、m=2、互异同模3单位根、
正基深和H≥1；根命中保留原深度∞，明确证明完整可测推前律，不使用非可测map默认值。

该结论仅针对观测接口，不是已知系数后的计算下界，也不是有限素数盒的分布相等。
16个完整序列直方图案例333768输入批次与3个反向控制仅为补充回归。独立数学/源码
复核通过；移动配置、素数传递、完整有符号分歧律、被动样本下界、三等距根停止律及
其他REC节点仍开放，整个包formalization_complete仍为false。此文档头不改已验Lean
代码、Audit或依赖，发布后仍需完整精确头CI和当前主分支检查。

# 2026-09-30 12:48 UTC — REC-L3 exact signed-depth law intake/reuse

Target: `docs/proofs/f3/prime_depth_reconstruction/proof.md` theorem2.1 equations2.2–2.3, theorem.md F3-REC-1, scaffolding REC-L3. Fixed distinct same-residue three-adic unit roots, actual normalized unit Haar samples, finite root distance L≥1. Root hits retain infinity and have proved zero measure. Define a signed atom by existence of two genuine finite integer depths with their signed difference h; do not assign an arbitrary integer to an infinite depth. Prove positive/negative atom reductions to exact layers and zero atom to equality, plus almost-everywhere finite coverage. Conditional sign/absolute-value independence is a separate remaining slice until actually proved.

Incremental intake: 175 actual remote branch heads at12:47. Original155 branch records compared using stored source SHA (two explicitly unrelated records have no eligible last_scanned_commit); only master moved through our already reviewed engineering PRs.20 new heads are our own implementation/correction branches. Updated issues/PRs since11:09 are only PR58–61. No newly observed external proof package; retain original bounded source watermarks and broader unfinished intake.

Final-target-first searches: GitHub queries `repo:leanprover-community/mathlib4 "padic" "distribution"`, `repo:leanprover-community/mathlib4 "valuation" "Haar"`, `"f3RootDepthDifference"`, `"rootDepth" "signed" language:Lean`; web `Lean formalization p-adic valuation difference Haar geometric distribution`, `site:github.com Lean "valuation" "conditional" "Haar"`. No exact final signed two-root law found in inspected results. This is bounded, not an exhaustive absence claim. Mathlib Padics/Measure/Monoid is the previously rejected abstract p-adic-valued distribution/convolution theory, not this real Haar law. The single signed-rootDepth external hit OVVO-Financial/RH_Lean@ca4aeadddbc97e37753206d6f2d0cf310d47de12 research/HALF_ROOT_PRIME_PAIR_WEIGHT.lean was read: reciprocal Mertens hyperbolic prime-pair shells, unrelated to additive three-adic depth. No code copied or dependency added.

Direct reuse at consumer pin mathlib5ed2965256430c3649e86755f9576b54eca72435:
- `Mathlib/RingTheory/Valuation/Basic.lean`: AddValuation.map_add_eq_of_lt_right and map_sub_eq_of_lt_left/right are genuine proofs under Ring and ordered additive valuation target. Strict comparison forces exact minimum. Root distance/depth use existing Padic.addValuation and already verified project min certificates. No valuation foundations rebuilt.
- `Mathlib/MeasureTheory/OuterMeasure/AE.lean`: ae_iff exactly equates almost-everywhere predicate with zero measure of its complement; measure_congr preserves measure under a.e. set equality. Reuse singleton nullity to cover finite depths a.e.
- Already verified project F3RootDepthLaw exact positive layer, F3RootBatchHaar equal-depth complement law, F3RootDepthNull singleton nullity, F3TruncatedNonidentifiability standard Borel measurability. These are actual Haar facts, not assumed PMFs.

Pinned source and current mathlib master6bd5e549d902323693ddf9128120376848331c85 were independently fetched at12:45–12:48. The named valuation and AE APIs remain available with the inspected signatures. Apache-2.0 notices on mathlib files verified. Existing project provenance retained. Do not upgrade dependencies. Current-source search hits are not evidence for pinned elaboration. Precise source links: https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/RingTheory/Valuation/Basic.lean and https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/OuterMeasure/AE.lean .

Decision: thin independent event adapter over existing kernel-verified local Haar layers, null roots, and generic valuation/measure APIs. Add all new declarations once to Audit; retain exact dependency pins and complete Actions gates. Source/API inspection and finite enumerations are not kernel acceptance.

## 2026-09-30 13:06 UTC：真实有符号深度原子律通过精确 CI

代码744ec233e8ff7d4b55455743848db377cc353b1e，树030bf991d04063ae1405fc083706c635decc7984，
[push36718612456](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36718612456)与
[PR36718619580](https://github.com/UyNewNas/omega-balance-prime-lean/actions/runs/36718619580)
完整成功；实际测试合并ad9ed10c6a4485169ee1af58d4eefb6b84346044文件树相同。首轮仅有
零事件证明的集合成员展开和自然数转WithTop有限性两处编译问题，已用显式change及
锁定库WithTop.natCast_ne_top修正，十五条公开陈述和全部定义没有改变。

十五条新声明均仅标准公理；793项总输出（792项目+1产生器）、115项目源文件、650依赖
模块与版本锁、构建、内核回归、逐一覆盖及144240有限检查通过。独立数学源码复核
通过；12个剩余类案例9360代表元仍只是补充回归。

验收范围为REC-L3/式(2.2)的实际无条件有符号原子律：所有正h与负h的质量为
3^(-(L+h))，零质量1−3^-L，并证明有限整数原子几乎处处覆盖。实际根命中仍为∞且
不属于有限差原子，零测例外已单独证明；原共享根单位/同余/正基深前提保留。
条件绝对值分布、符号独立性、移动配置、素数转移、被动下界和三等距根等仍开放，
整个REC包formalization_complete=false。最终状态头只改文档，仍另行完整精确CI。

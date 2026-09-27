# F₃ 全量形式化推进 — Round 24

日期：2026-09-27

## 本轮精确基线

- 工作链：PR #26 `feat/f3-bftb-crt-package-v1` → PR #27 `feat/f3-bftb-residue-block-v1`。
- 本轮最终数学源码 exact head：`0d5e9c3a9433eb43d0b773bf16da363ef528a0c8`。
- Lean workflow run `36299729802`：SUCCESS。
- Factor-sum workflow run `36299729796`：SUCCESS。
- Axiom audit：565 declarations，仅标准 Lean axioms。
- Source audit：86 Lean files，无 proof escape。
- Declaration coverage：565/565 exactly once。
- 有限 F₃ 回归：144240 PASS。

## 本轮新增已验证接口

`OmegaBalance/F3BFTBResidueBlock.lean`

- `bftb_consecutivePrimeBlock_prefix_modEq`：
  有序 prime-pattern 前缀在 `D ∣ g` 且 offset 全落在 `a mod D` 时保持同一剩余类。
- `bftb_consecutivePrimeBlock_prefix_diameter`：
  offset 位于 `[lo,hi]` 时，真实连续素数块直径显式 `≤ hi-lo`。
- `bftb_consecutivePrimeRunInClassBounded_of_exact_prefix`：
  exact affine prime pattern + `card ≥ L` 组装为长度恰为 `L` 的
  `ConsecutivePrimeRunInClassBounded`。
- `bftb_consecutivePrimeRunsInClassBounded_of_infinite_exact_prefix`：
  固定 exact pattern 若对无限多个平移参数出现，则对任意下界都有同一显式直径界的真实连续素数块。

`OmegaBalance/F3BFTBResidueAssembly.lean`

- `bftb_full_exact_prime_pattern_infinite_of_outside_composite`：
  tuple 内 exact pattern 的无限性在 tuple 外统一合数时提升为整个有限 ambient interval 的 exact pattern 无限性。
- `bftb_consecutivePrimeRunsInClassBounded_of_many_primes_and_outside`：
  将“protected tuple 中 infinitely often 至少 L 个素数”与 ambient interval 外部位置统一合数
  组合成任意远的、全体素数序列中的、同一剩余类的长度 L 连续素数块。
  这一步只假设显式 many-primes 输入，不把 BFTB/Shiu 连续素数结论本身作为假设。

所有 6 条新 theorem 均在 `scripts/Audit.lean` 一对一登记。

## 当前 blocker：真正的无条件 many-primes producer

本轮重新核对两个上游：

1. `AxiomMath/PrimeGapsLib@1faa7b14e82ddebc2772dfb9153922f01b106477`
   的 `PrimeGaps.lem_main_conclusion` 已给出 admissible indexed tuple 中 infinitely often many primes，
   但它显式要求 `BombieriVinogradov` 参数；该项目的 `BombieriVinogradov` 只是 Prop 假设。
   证明中该参数首先被转成
   `Nat.HasLevelOfDistribution Set.univ θ 1`。

2. `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`
   确实有无条件
   `fourFactor_standardBombieriVinogradov :
     MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov`。
   但该 StandardBV 使用 prefix-max AP error、`Li(x)` 主项和
   `N^(1/2)/log(N)^B` cutoff；PrimeGapsLib 的接口使用 `π(x)` 主项和 `x^θ` cutoff，
   因此仍需真实的 normalization/cutoff bridge，不能靠改名或类型强转。
   Liu--Wang 固定 Lean 4.33.0-rc1 / mathlib `e4c91783...`；本仓库固定
   Lean 4.34.0 / mathlib `5ed29652...`。

本仓库的 ANT pin `099d3726...` 本身保留了若干 Liu--Wang 的同 pin 兼容切片，
但没有上述 StandardBV endpoint 模块；本轮没有对 ANT 做无关改动。

## 下一子任务

优先把 RUN 的解析依赖收敛到一个可审计接口：
- 证明或迁移 StandardBV → PrimeGaps 所需 level-of-distribution/BV 形状的桥；
- 核验 PrimeGaps many-primes endgame 在本仓库固定 Lean/mathlib 上的最小兼容依赖；
- 再把该无条件 producer 接到本轮已经 exact-green 的
  `bftb_consecutivePrimeRunsInClassBounded_of_many_primes_and_outside`。

停止条件未满足；不合并 master，不把条件 many-primes 输入冒充最终 RUN 定理。

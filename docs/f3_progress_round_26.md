# F₃ 全量形式化推进 — Round 26

日期：2026-09-27

## 精确基线

- stacked PR #28: feat/f3-bftb-bv-normalization-v1
- exact source head: dc48b766ba9d7c150c9a52d4abb1259078db90c9
- Lean run 36304998998: SUCCESS
- Factor-sum run 36304998960: SUCCESS
- exact gates: 575 declarations; only standard Lean axioms; 88 Lean files with no
  proof escapes; Audit coverage 575/575 exactly once; finite F₃ checks 144240 PASS.

## 本轮实际推进

建立 feat/f3-bftb-bv-residue-max-v1，并新增
OmegaBalance/F3BFTBBVResidueMax.lean。目标是把已验证的逐 residue
Li-to-pi 主项正规化提升到 PrimeGaps 实际使用的 finite supremum 形状。

新增接口：
- bftb_iSup_abs_main_term_change_totient
- bftb_sum_iSup_abs_main_term_change_totient

第二条允许 residue type 随 q 变化为 (ZMod q)ˣ，因此和 PrimeGaps
BombieriVinogradov 的模数求和接口一致。两条均加入 scripts/Audit.lean。

## 上游接口复核

Liu--Wang StandardBombieriVinogradov 使用 genuine Li 主项、prefix max 和
panModulusCutoff。PrimeGaps BombieriVinogradov 使用 pi 主项、(ZMod q)ˣ 上的
iSup 和 floor(x^theta) cutoff。上一轮已 exact-green 关闭 fixed theta<1/2 的
cutoff inclusion；本轮关闭 residue-iSup normalization seam。

仍缺的解析层是把 Liu--Wang 的 canonical unitResidues/max' 与
PrimeGaps 的 ZMod-unit iSup 精确识别，并把 q=1 的 StandardBV 误差用于控制
|Li-pi|，再以 reciprocal-totient polylog sum 吸收 normalization loss。

停止条件未满足；不得把本轮 seam 解释成无条件 BV 或最终 BFTB RUN。

## 第一轮 CI 失败与修复

commit a0e8d5d011eeabcf630035e248cc25c2c49c5797 的 Lean run
36305493941 在 F3BFTBBVResidueMax.lean:28 失败。原因是
add_le_add_right 生成了加数方向相反的目标，并非数学缺口。修复为显式
add_le_add (le_ciSup hbdd a) (le_refl _)；修复 commit 必须重新通过完整门禁后
才能把两条新 theorem 标记为 exact-green。

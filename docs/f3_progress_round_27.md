# F₃ 全量形式化推进 — Round 27

日期：2026-09-27

## 精确基线

- parent exact-green source head: `58bd5ee8824e171eda231c5185a92b88b629eeff`
- branch: `feat/f3-bftb-unit-residue-equiv-v1`
- 上一层已完成 `(ZMod q)ˣ` 上 Li→π 的 iSup / modulus-sum normalization。

## 本轮实际目标

关闭 Liu--Wang 新版 canonical residues `(range q).filter (fun l => l.Coprime q)` 与 PrimeGaps `(ZMod q)ˣ` 索引之间的有限等价层，并保留 q=0/q=1 边界。

新增候选接口：`bftbUnitResidues`、`mem_bftbUnitResidues`、`bftbUnitResidues_zero`、`bftbUnitResidues_one`、`bftb_unit_val_mem_residues`、`bftbUnitResidueEquiv`、`range_score_unit_eq_range_residue`。

所有 theorem/lemma 均登记到 `scripts/Audit.lean`。等价本身是定义，不单列 axiom audit。必须以 exact-head CI 为准。

## 下一步

本层 exact-green 后继续证明 canonical finite `max'` 与 unit-indexed `iSup` 精确相等，再连接 Liu--Wang `standardPrimeAPMaxError` / prefix-max error，随后处理 q=1 项与 reciprocal-totient normalization loss。

## Exact-head 验证与继续推进

commit `88c232c1201b787025ac413efdde658520932780` 已通过 Lean run `36307227853` 与 Factor-sum run `36307227847`：582 declarations，仅标准 Lean axioms；90 Lean files 无 proof escape；Audit 582/582 exactly once；144240 finite checks PASS。

在此 exact-green 基线上继续候选实现 canonical finite `max'` = unit-indexed `iSup`，新增 `bftbUnitResidueEquiv_val` 与 `bftbCanonicalResidueMax_eq_iSup`；仍须新的 exact-head CI 后才可标绿。

## 验证补充

766b743a442603f22d573a6ced835b13f992c36a 已通过 Lean 36307522769 与 Factor-sum 36307522685。门禁为 584 declarations、90 Lean files、Audit 584/584、有限检查 144240 PASS。canonical max 与 unit supremum 层因此转为 verified。下一切片为 modulus-one AP compatibility，尚待新的 exact-head CI。

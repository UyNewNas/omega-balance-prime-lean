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

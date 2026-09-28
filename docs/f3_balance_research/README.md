# F₃ research rounds

## 固定保存位置

- Branch: `codex/f3-balance-research-docs`
- Directory: `docs/f3_balance_research/`
- New round filename: `notes_roundN.md` (N is the mathematical round number).

每轮先读取本目录最新轮次与仓库 AGENTS.md。增加下一轮笔记，不覆盖、移动或重命名旧研究记录。新推导、引用定理、实验和未完成目标须明确区分。固定提交位置不是自动运行计划。

## 历史与当前索引

|轮次|笔记|
|---:|---|
|1|[research_notes.md](research_notes.md)|
|2|[research_notes_round2.md](research_notes_round2.md)|
|3|[research_notes_round3.md](research_notes_round3.md)|
|4|[research_notes_round4.md](research_notes_round4.md)|
|5|[research_notes_round5.md](research_notes_round5.md)|
|6|[research_notes_round6.md](research_notes_round6.md)|
|7|[research_notes_round7.md](research_notes_round7.md)|
|8|[notes_round8.md](notes_round8.md) — 本轮补存原始全文，保留其历史状态说明|
|9|[notes_round9.md](notes_round9.md) — 全层正规形与逐线增长预筛|

其他研究：[F3_fixed_gaps.md](F3_fixed_gaps.md)。其独立记录不由本次提交覆盖。

## 第九轮复现

```sh
python3 docs/f3_balance_research/verify_round9.py --out /tmp/f3-round9-check
```

该脚本仅使用 Python 标准库。`verification_results_round9.json` 保存本次实际运行输出；`provenance_round9.json` 记录源文件和证据哈希。有限核验不是 Lean 形式化或素数无穷性证明。本次不更改 Lean 源码、默认导入、工具链或 CI。

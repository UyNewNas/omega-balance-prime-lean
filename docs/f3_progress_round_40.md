# F₃ 全量形式化推进 — Round 40

- 新增 `F3BFTBMaynardAdapter.lean`，提交 `2d8d43bd42c3727771c102fc18fb0edb2f3d80ac`。
- 默认库导入提交 `637dde4b939e0c7aa14f84527479a9c08691ccff`。
- Audit 登记提交 `2c5db92d1655ed963a58e47612f37982492e5337`。
- RUN-1/RUN-2 仍未登记完成：当前必须先让 pinned `lean-proofs-latest` 在仓库锁定 Lean/mathlib 下通过依赖准备、构建和完整审计。
- 上游生产者为 `MaynardBFT.consecutive_primes`；本地 adapter 保留 full-prime consecutiveness、任意晚起点和 `D*C` span。
- 下一步：解决 downstream `post_update` 路径兼容并取得 exact-head CI；失败时只按真实日志修复。

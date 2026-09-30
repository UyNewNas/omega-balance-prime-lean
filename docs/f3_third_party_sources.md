# F3 外部来源与许可范围说明

F3 连续素数段（RUN）的上游形式化工作来自以下项目。感谢原作者、维护者及贡献者；本项目的兼容修改不改变原始工作的归属。

- **plby/lean-proofs**：由 GitHub 用户 [plby](https://github.com/plby) 维护，使用固定提交 [`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e) 的 `src/latest`，包括 RUN 所需的 BFT 产生器及其依赖。作者与贡献记录以该固定版本的源码和 Git 历史为准。
- **frenzymath/FormalPantheon**：使用固定提交 [`ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`](https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1) 的 `BoundedGaps`。该版本根目录的 [Apache-2.0 许可证](https://github.com/frenzymath/FormalPantheon/blob/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/LICENSE) 与原始署名保留。

集成方式是固定版本的外部 Lake 依赖，加上本仓库记录的少量、带来源哈希校验的兼容补丁；未将 plby 的完整原创源码闭包复制进本仓库。具体版本、修改范围与验证记录见 [复用记录](f3_external_reuse.md) 和 `lake-compat/run-compatibility.json`。

plby 该固定版本的 [`src/latest/LICENSE`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE) 涵盖部分外部来源文件；其原创 BFT 源码闭包的许可范围尚未确认。本说明不表示已获得该部分的许可，也不将未收到联系视为授权。署名及下述处理承诺不能替代许可证。

如权利人认为本仓库对相关第三方代码的使用涉及其权利，请通过 [本仓库 Issues](https://github.com/UyNewNas/omega-balance-prime-lean/issues) 联系并指出相关代码。收到联系后，我们会及时处理、移除受影响的第三方代码。

技术集成继续推进；任何形式化完成或合并声明仍须通过精确版本的 Lean 构建、回归、公理、源码及覆盖审计。许可范围尚未确认这一事实会继续明确保留。

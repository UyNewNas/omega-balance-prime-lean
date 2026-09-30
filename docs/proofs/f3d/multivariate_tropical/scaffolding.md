# F3D-MULTI：引理脚手架与审计记录

状态分项：MULTI-1/2、构造方向、有限热带表达式 Lipschitz 界与固定幅度开关保留 PAPER-AUDITED；必要性与依赖它的全体可实现函数结论为 RESEARCH（审计缺口）。

[定理](theorem.md) · [完整证明](proof.md) · [PDF](paper.pdf) · [形式化计划](formalization.md)

## 1. 证明节点

| ID | 职责 | 状态 |
|---|---|---|
| MULTI-L1 | 和差比 x=(n+d)/(n-d) 满足 F=v3(x) | 审计通过 |
| MULTI-L2 | 二次正性检测 Theta | 审计通过 |
| MULTI-L3 | mu(x,y) 实现两输入最小值 | 审计通过 |
| MULTI-L4 | xy/mu(x,y) 实现最大值 | 审计通过 |
| MULTI-L5 | H_k=sum 3^i x_i^k 的唯一最低项公式 | 审计通过 |
| MULTI-L6 | 从相邻幂提取最小值与第一极小位置 | 审计通过 |
| MULTI-L7 | 有限 min/max 表达式 = 两个整数热带多项式之差 | 审计通过 |
| MULTI-L8 | 热带表达式的固定有理函数实现 | 审计通过 |
| MULTI-L9 | 有理函数清分母、多重齐次化回到整数多项式对 | 审计通过 |
| MULTI-L10 | 合法整数输入的有限单位网格参数化 | 审计通过 |
| MULTI-L11 | Lagrange 网格插值界 | 审计通过 |
| MULTI-L12 | 固定网格赋值的有限仿射分区与热带性 | 原有限分区论证保留、此次不重审；“等价热带表达式”已被反例否定并撤回 |
| MULTI-L13 | 网格最小值恢复 g=eta_A-eta_B | 审计通过 |
| MULTI-L14 | 多输入必要性：所有可实现 g 都是有限整数热带表达式 | RESEARCH；L12 热带断言失效，当前路线阻塞 |
| MULTI-L15 | 有限整数热带表达式的全局 Lipschitz 常数 | 审计通过；推广到全部可实现函数的当前路线为 RESEARCH |
| MULTI-L16 | 无界条件开关 | 非热带性保留；多项式不可实现的当前路线为 RESEARCH |
| MULTI-L17 | 固定幅度条件开关可实现 | 审计通过 |
| MULTI-L18 | 任意素数 p 的最小值公式 | 审计通过 |

## 2. 依赖 DAG

```text
MULTI-L1 -> MULTI-L2 ------------------------------> F3D-MULTI-1
        -> MULTI-L3 -> MULTI-L4 -------------------> F3D-MULTI-2
        -> MULTI-L5 -> MULTI-L6 -------------------^

MULTI-L7 -> MULTI-L8 -> MULTI-L9 -> MULTI-3 构造方向（保留）
MULTI-L10 -----------------------> MULTI-L13（恢复恒等式，保留）
MULTI-L11（网格最小值插值界，保留）
MULTI-L12 热带等价断言（已撤回） -X-> MULTI-L14 / MULTI-3 必要性
MULTI-L15（热带函数 Lipschitz，保留） -> MULTI-L16 非热带性（保留）
MULTI-3 必要性（缺口） -X-> MULTI-4 全体可实现函数界 / 开关不可实现
MULTI-L7/L8/L9 -> MULTI-L17 / MULTI-4 固定幅度开关（保留）
MULTI-L3 -> MULTI-L18
```

## 3. 关键审计点

### 3.1 二次正性检测没有最低项抵消

v3(u^2)=2a，而 v3(3v^2)=1+2b，一个偶数一个奇数，因此永不相等。

同时 v3(u^2+v^2)=2 min(a,b)；等层时两个单位平方模 3 都为 1，其和为 2，不被 3 整除。

### 3.2 最小值构造全域无零极点

x^2+3y^2=0 会要求有理平方等于 -3；x^3+3y^3=0 会要求有理立方等于 -3。两者均不可能。

### 3.3 批量 H_k 的唯一最低项

若某个输入赋值比最小值至少大 1，乘上 k>=m 后产生至少 m 的优势，足以压过编号偏移的最大差 m-1；若赋值并列，最小编号 i0 唯一胜出。因此 H_k 非零。

### 3.4 必要性使用真实整数输入

对任意 t_i in Z，取 u_i=2*3^{t_i^+} s_i、v_i=2*3^{t_i^-} r_i，再令 n_i=(u_i+v_i)/2、d_i=(u_i-v_i)/2。这样得到实际整数输入并精确满足 F(X_i)=t_i。

### 3.5 插值界的常数来源

一变量节点 1,4,...,1+3D 的 Lagrange 分母为 3^D j!(D-j)!（差一个符号），故赋值至多 D+v3(D!)。对 ell 个变量张量化，损失至多 ell(D+v3(D!))。

### 3.6 为什么不必枚举 2^m 个抵消模式

原有限仿射分区的抵消递归论证保留，但有限分区不等价于有限热带表达式。proof.md §9.2 的合法三输入二次多项式对给出距离 1、跳幅 2M+1 的固定网格值；这直接否定热带等价断言，不否定允许不连续的分区性质。

### 3.7 直接取网格最小值即可恢复输出

全域实现给出 v3(A(t;omega))-v3(B(t;omega))=g(t) 对每个网格点 omega 都成立。因此 min_omega v3(A)=min_omega v3(B)+g，即 g=eta_A-eta_B。此恒等式不使用 L12；但它不自动证明 eta_A、eta_B 或 g 的热带表示性，不能闭合必要性。

### 3.8 无界开关的非热带性与不可实现性缺口

条件检测 H(t)=1_{t>=0} 和固定幅度开关可以实现。跨条件边界的输出跳幅 |G(0,M)-G(-1,M)|=M 无界，说明 G 不是有限整数热带表达式；推广为多项式不可实现的当前路线依赖有缺口的 MULTI-L14。

## 4. 文献边界

Tran–Wang 研究 tropical rational functions 的表示复杂度；Koutschan–Moser–Ponomarchuk–Schicho 研究连续分段线性函数的 min/max/max-linear 表示。本包不把一般热带表示理论作为新贡献。

当前登记的精确表达能力等价仍是待修复目标；构造方向保留。是否已有完全相同表述，尚未完成系统文献查新。

## 5. 审计结论

2026-09-30 边界复核确认 `F3D-CORR-MULTI-L12`：原“未发现缺口”的整体结论撤回。MULTI-L12 的热带等价断言被合法反例否定；MULTI-L14 及依赖它的 MULTI-4 全体可实现函数路线降为 RESEARCH，等待实质修复。

MULTI-1/2、MULTI-3 构造方向、MULTI-L13 恢复恒等式、MULTI-L15 的有限热带范围及 MULTI-L17 固定幅度开关保留原分项书面状态。本次没有重新认证整个理论，也没有主分类的反例：见证中 A=B，输出 g=0。详见 [修正报告](../../../../reports/f3d_proof_boundary_corrections.md)。

## 6. PDF 门禁

paper.tex 由 proof-PDF workflow 生成 paper.pdf，并执行 XeLaTeX、pdfinfo 与全页 Poppler render check。

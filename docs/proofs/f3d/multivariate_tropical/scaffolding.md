# F3D-MULTI：引理脚手架与审计记录

状态：PAPER-AUDITED。

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
| MULTI-L12 | 固定网格值的赋值为有限整数仿射分区函数 | 审计通过 |
| MULTI-L13 | 网格最小值恢复 g=eta_A-eta_B | 审计通过 |
| MULTI-L14 | 多输入必要性：所有可实现 g 都是有限整数热带表达式 | 审计通过 |
| MULTI-L15 | 全局 Lipschitz 常数 | 审计通过 |
| MULTI-L16 | 无界条件开关不可实现 | 审计通过 |
| MULTI-L17 | 固定幅度条件开关可实现 | 审计通过 |
| MULTI-L18 | 任意素数 p 的最小值公式 | 审计通过 |

## 2. 依赖 DAG

```text
MULTI-L1 -> MULTI-L2 ------------------------------> F3D-MULTI-1
        -> MULTI-L3 -> MULTI-L4 -------------------> F3D-MULTI-2
        -> MULTI-L5 -> MULTI-L6 -------------------^

MULTI-L7 -> MULTI-L8 -> MULTI-L9 ------------------\
MULTI-L10 -> MULTI-L11 -> MULTI-L12 -> MULTI-L13 ---+-> F3D-MULTI-3
                                                       |
F3D-MULTI-3 -> MULTI-L15 -> MULTI-L16/L17 ----------+-> F3D-MULTI-4
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

固定单位网格点后，多项式只有有限项。按单项赋值的有限仿射比较划分格点；最低项并列时，归一化后的单位系数和是固定整数。若抵消则删去一组，若不抵消则只产生固定赋值修正。项数有限，所以递归有限终止。

### 3.7 直接取网格最小值即可恢复输出

全域实现给出 v3(A(t;omega))-v3(B(t;omega))=g(t) 对每个网格点 omega 都成立。因此 min_omega v3(A)=min_omega v3(B)+g，即 g=eta_A-eta_B。无需再单独证明有界修正 delta 的表示性。

### 3.8 无界开关失败的真正原因

条件检测 H(t)=1_{t>=0} 可以实现；失败的是跨条件边界的输出跳幅 |G(0,M)-G(-1,M)|=M 无界，而所有有限整数热带表达式都有统一 Lipschitz 常数。

## 4. 文献边界

Tran–Wang 研究 tropical rational functions 的表示复杂度；Koutschan–Moser–Ponomarchuk–Schicho 研究连续分段线性函数的 min/max/max-linear 表示。本包不把一般热带表示理论作为新贡献。

当前登记的是固定整数多项式对在 F_{3,D} 全域算术模型中的精确表达能力等价；是否已有完全相同表述，尚未完成系统文献查新。

## 5. 审计结论

本轮根据用户提供的 f3d_multivariate_tropical_realization.md 内容重新展开并核对：二次正性检测、双输入 min/max、批量最小值与第一极小位置、构造方向的全域无零极点与清分母、多输入必要性的真实整数网格参数化、Lagrange 插值界、抵消递归有限性、Lipschitz 不可能性与固定幅度开关。

未发现影响 F3D-MULTI-1/2/3/4 的书面证明缺口。

## 6. PDF 门禁

paper.tex 由 proof-PDF workflow 生成 paper.pdf，并执行 XeLaTeX、pdfinfo 与全页 Poppler render check。
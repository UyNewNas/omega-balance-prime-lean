# F₃ 的整数延拓与运算规则

日期：2026-09-24。本文记录本轮数学推导及其形式化边界。

## 1. 三个层次不能混淆

| 层次 | 内容 | 验证方式 |
|---|---|---|
| Lean 证明 | 整数延拓、零点分类、平方、立方、迭代立方、乘法层级、修正间距、固定和反射 | `lake build` 与完整公理审计；以对应提交的 CI 为准 |
| 有限计算 | 千万以内分布、同值段、144,240 项公式检查、边界回归 | 标准库 Python，不能代替无限性证明 |
| 外部解析数论定理 | 等差数列素数定理；指定余数类中的连续素数串 | 第 8 节文献输入；本仓库未形式化，也没有添加为公理 |

这里没有孪生素数无穷性的证明，也不主张基本赋值运算是新的数论定理。

## 2. 定义和定义域

原来的 `f3 : ℕ → ℤ` 已经定义在所有自然数上：

```math
F_3(n)=v_3(n+1)-v_3(n-1).
```

`n-1` 在自然数中是截断减法；有通常数论意义的运算公式使用 `n>1`。
新增真正的有符号整数接口：

```lean
v3Int (z : ℤ) : ℕ
f3Int (z : ℤ) : ℤ
```

其中 `v3Int z = padicValInt 3 z`，非零时等于对 `|z|` 计数因子 3。
`f3Int z` 的两个邻数均先在 ℤ 中计算。

- `f3Int_nat`：在 `1 ≤ n` 下，与旧 `f3 n` 完全兼容。
- `f3Int_neg`：对所有整数，`f3Int (-z) = -f3Int z`。
- `f3_eq_zero_iff_three_dvd`：`n>1` 时，`f3 n = 0 ↔ 3 ∣ n`，不需要素数性。

**零处约定：** Lean 沿用 mathlib 的 `v3 0 = v3Int 0 = 0`，这是全函数约定，不是普通赋值中“零只有零个因子 3”。例如加法最小值定理必须排除和为零；精确最小值公式还排除各项为零。Python 中普通 `v3(0)` 则主动报错，测试中的 `total_v3` 显式实现全函数适配。

## 3. 层级、平方与立方

以下设 `n>1` 且 `3 ∤ n`。模 3 余 2 时 `F₃>0`，余 1 时 `F₃<0`，仅一侧邻数有因子 3。因此：

```math
|F_3(n)|=v_3(n-1)+v_3(n+1)=v_3(n^2-1).
```

对应 `f3_abs_eq_neighbor_sum`、`f3_abs_eq_v3_sq_sub_one`。

平方定理 `f3_sq`：

```math
F_3(n^2)=-|F_3(n)|.
```

因为 `n²≡1 (mod 3)`，而 `n²-1=(n-1)(n+1)`。

立方定理 `f3_cube`（在 Lean 中用正负分支表达）：

```math
F_3(n^3)=F_3(n)+\operatorname{sgn}(F_3(n)).
```

证明用 `n³-1=(n-1)(n²+n+1)` 或 `n³+1=(n+1)(n²-n+1)`；对应的二次因子恰好含一个 3。这两个精确赋值也分别有公开引理。

`f3_iterated_cube_pos` 和 `f3_iterated_cube_neg` 分别证明：

```math
F_3(n^{3^r})=
\begin{cases}
F_3(n)+r,&n\equiv2\pmod3,\\
F_3(n)-r,&n\equiv1\pmod3.
\end{cases}
```

例：`F₃(5)=1`，`F₃(25)=-1`，`F₃(125)=2`；`F₃(7)=-1`，`F₃(343)=-2`。幂运算产生的通常是合数，不能称为新素数生成公式。

## 4. 乘法规则

令 `s(n)=f3Side n`：模 3 余 2 时取 +1，否则取 -1。在 `n>1, 3∤n` 的定义域内，它是 `F₃(n)` 的符号；`f3_eq_side_mul_natAbs` 证明

```math
F_3(n)=s(n)|F_3(n)|.
```

对 `m,n>1`、`3∤mn`：

```math
s(mn)=-s(m)s(n),
\qquad
|F_3(mn)|\ge\min(|F_3(m)|,|F_3(n)|).
```

两个输入层级不同时，后一式取等号。接口是 `f3Side_mul`、`f3_mul_depth`。

Lean 证明使用

```math
(mn)^2-1=(m^2-1)n^2+(n^2-1),\qquad v_3(n^2)=0
```

及赋值的超度量性质。同层时可能抵消并升层，例如 `F₃(2)=1`、`F₃(4)=-1`，但 `F₃(8)=2`；所以不能删除“层级不同”前提。

## 5. 修正间距的精确赋值

对任意 `p,q>1`、`3∤pq`，令 `a=|F₃(p)|, b=|F₃(q)|`、`s=s(p), t=s(q)`。

`p+s` 与 `q+t` 是被 3 整除的一侧邻数，赋值分别为 a,b。若 a≠b，则

```math
v_3\big((q-p)+t-s\big)=\min(a,b).
```

接口 `f3_adjusted_gap_valuation` 不要求素数性，也不要求 p<q；修正间距在 ℤ 中计算，负数通过绝对值取赋值。不同层级保证该赋值参数非零。

若 p<q，写 h=q-p，则同号对应 `v₃(h)`，前正后负对应 `v₃(h-2)`，前负后正对应 `v₃(h+2)`。

这只刻画已有候选的位置；不保证候选是素数，也不产生短间距素数对的存在性。

## 6. 固定总和的反射规则

`f3_reflection` 的实际前提比最初的素数表述更弱：

```math
a,b>1,\quad 3\nmid a,\quad 3\mid a+b,\quad
|F_3(a)|<v_3(a+b)
\quad\Longrightarrow\quad F_3(b)=-F_3(a).
```

总和无需是偶数，两项无需是素数。因为两项模 3 相反，故 s(b)=-s(a)。设 N=a+b，则

```math
b+s(b)=N-(a+s(a)).
```

右侧两项赋值不同，差的赋值等于较小者，即 `|F₃(a)|`。

例：`54=17+37` 给出 `+2,-2`；奇数总和 `9=2+7` 同样适用。
严格不等号不能改为等号：`30=11+19` 中 `|F₃(11)|=v₃(30)=1`，而 `F₃(19)=-2`。

## 7. 如何复现

固定工具链与 mathlib 修订保持不变，按仓库构建配置运行：

```sh
lake update
lake exe cache get
lake build
lake build OmegaBalance.Examples OmegaBalance.F3Examples
python3 scripts/verify.py
python3 scripts/f3_corollaries_verify.py --limit 10000000
python3 scripts/test_f3_corollaries.py
```

`Audit.lean` 导入回归模块并对每条新 theorem 执行 `#print axioms`。仅接受已有三个标准公理；源码扫描不允许证明占位或原生决定过程逃逸。

`reports/f3_corollaries_1e7.txt` 保存一次实际运行。随机种子固定；耗时可能变化。144,240 项主检查包括一般幂公式的有限核验；**任意指数的完整幂公式目前仅在计算中检查，Lean 本轮正式证明的是平方、立方和迭代立方。**

## 8. 外部定理的推论：文献层，不是 Lean 层

### 固定取值的密度

固定 k≥1，`F₃(p)=k` 对应模 `3^(k+1)` 的两个互素余数类
`3^k-1`、`2·3^k-1`；负值对应 `3^k+1`、`2·3^k+1`。
由固定模数的等差数列素数定理，各自的相对素数密度为 `3^(-k)`。
层级≥K 对应模 `3^K` 的 ±1 两个类，密度为 `3^(-(K-1))`。
这不意味着相邻素数的 F₃ 值独立，也不能不经一致性分析便令 k 随 x 增长。

参考：K. S. Kedlaya, *Notes on analytic number theory*, Chapter 4, especially §4.4:
<https://kskedlaya.org/ant/chap-primes-in-ap.html>。

### 连续素数上的任意长同值段

固定非零值 ±k，选上面任一个对应的互素余数类；指定余数类中的连续素数长串定理便给出任意长的恒值段。这是“同值”，不能替换为“两个指定的相反值同时在短区间中出现”。

参考：W. D. Banks, T. Freiberg, C. L. Turnage-Butterbaugh,
*Consecutive primes in tuples*, arXiv:1311.7003v3 (2014), Corollary 3:
<https://arxiv.org/abs/1311.7003>。

上述参考在本轮查阅；没有把论文定理加入 Lean 的自定义公理。

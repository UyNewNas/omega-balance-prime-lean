# F₃：二次切触、赋值差分权与素数对相关接口

日期：2026-09-28。
状态：下文局部恒等式有纸面证明及有限核验；未在本轮进行 Lean 形式化。素数权抵消只有计算观察，没有得到其渐近估计或孪生素数无穷性证明。本文不声称局部公式在文献中首次出现。

## 1. 定义与边界

对正整数 n>1，记

\[
F_3(n)=v_3(n+1)-v_3(n-1).
\]

赋值在非零整数上按绝对值定义。本文不把 v₃(0) 定义为有限整数；整除指标在 0 处仍然有意义。有限和使用整除指标，因此与 Lean / mathlib 的全函数零值约定无关。

给定 r≥1，定义整数值的赋值差分权

\[
W_r(z)=3\mathbf1_{3^{2r}\mid z}-\mathbf1_{3^{2r-1}\mid z}.
\]

它在 3^{2r}|z 时为 2，在 v₃(z)=2r−1 时为 −1，其余为 0；W_r(0)=2。

若 n>1、h≥0，则

\[
W_r(n(n+h)+1)
=3\mathbf1_{F_3(n(n+h))\ge2r}
 -\mathbf1_{F_3(n(n+h))\ge2r-1}.
\]

原因是 n(n+h)±1 不会同时被 3 整除：任一正深度阈值可直接由 F₃ 读取。

## 2. 孪生位移的二阶切触

令 P_h(x)=x(x+h)+1。它的判别式为 D_h=h²−4，并有

\[
4P_h(x)=(2x+h)^2-D_h.
\]

h=2 时 P₂(x)=(x+1)²，因而

\[
W_r(n(n+2)+1)=2\mathbf1_{3^r\mid n+1}
             =2\mathbf1_{F_3(n)\ge r}\quad(n>1).
\]

因此间距 2 上的权逐点非负，并不仅限于素数。

另一个精确的几何表述是

\[
-\frac1x-(x+2)=-\frac{(x+1)^2}{x}.
\]

在 x 为 3-进单位且 x≈−1 时，逆元曲线 q=−1/x 与直线 q=x+2 在 x=−1 二阶相切，差值赋值为 2v₃(x+1)。这解释了乘积加倍与深度—间距格点的共同来源。

## 3. 二次传递公式：完整证明

### 定理

对所有整数 h 和 r≥1，

\[
\boxed{
\sum_{n=0}^{3^{2r}-1}W_r(n(n+h)+1)
=3^rW_r(h^2-4).
}
\]

更一般地，对任意奇素数 ℓ，定义

\[
W_{\ell,r}(z)=\ell\mathbf1_{\ell^{2r}\mid z}
             -\mathbf1_{\ell^{2r-1}\mid z}.
\]

若 a,b,c 为整数且 ℓ∤a，则

\[
\boxed{
\sum_{n\bmod\ell^{2r}} W_{\ell,r}(an^2+bn+c)
=\ell^rW_{\ell,r}(b^2-4ac).
}
\]

所以这项局部机制不是 ℓ=3 独有。

### 证明

令 Q=ℓ^{2r}，D=b²−4ac。因 2a 是模 Q 的单位，变换 y=2an+b 是模 Q 的置换。又因 4a 是单位，

\[
W_{\ell,r}(an^2+bn+c)=W_{\ell,r}(y^2-D).
\]

将 y 唯一写成 u+ℓ^r v，其中 0≤u,v<ℓ^r。模 Q 下

\[
y^2-D\equiv u^2-D+2u\ell^r v.
\]

若 u=0，则每个 v 都贡献 W_{ℓ,r}(D)，本组贡献为 ℓ^rW_{ℓ,r}(D)。

若 u≠0，令 t=v_ℓ(u)<r。随着 v 遍历模 ℓ^r，线性项 2uℓ^r v 遍历由 ℓ^{r+t} 生成的子群，每个值重复 ℓ^t 次。若 ℓ^{r+t}∤u²−D，则两个整除指标都恒为零。若 ℓ^{r+t}|u²−D，则恰有 ℓ^t 个 v 使 Q|y²−D，恰有 ℓ^{t+1} 个 v 使 (Q/ℓ)|y²−D。因此本组的有符号贡献为

\[
\ell\cdot\ell^t-\ell^{t+1}=0.
\]

所有非中心组恰好抵消，只剩 u=0 组，定理得证。

本证明只用有限同余和整除计数，不依赖任何素数分布假设。

## 4. 短位移窗口内的精确隔离

令 Q=3^{2r}，并取整数 H 满足

\[
2\le H<3^{2r-1}-2.
\]

则对 2≤h≤H，

\[
\frac1Q\sum_{n\bmod Q}W_r(n(n+h)+1)
=
\begin{cases}
2/3^r,&h=2,\\
0,&h\ne2.
\end{cases}
\]

证明：当 h>2 时，h−2 和 h+2 均严格介于 0 与 3^{2r−1} 之间，而二者之差为 4，所以至多一个含有 3 因子。故它们的乘积不可能被 3^{2r−1} 整除。h=2 时判别式为 0。

r=3 时可以取 H=240，模数 Q=729。此时全部其他短位移的完整周期平均为零，间距 2 的平均为 2/27。

这个结论只涉及均匀模周期平均，绝不是逐点识别素数或素数对平均定理。

## 5. 根计数全谱

记

\[
R_R(h)=\#\{n\bmod3^R:3^R\mid n(n+h)+1\}.
\]

令 D=h²−4。若 D=0，则

\[
R_R(h)=3^{\lfloor R/2\rfloor}.
\]

若 D≠0，令 t=v₃(D)、u=D/3^t，则

\[
R_R(h)=
\begin{cases}
3^{\lfloor R/2\rfloor},&R\le t,\\
0,&R>t,\ t\text{ 为奇数},\\
0,&R>t,\ t\text{ 为偶数},\ u\equiv2\pmod3,\\
2\cdot3^{t/2},&R>t,\ t\text{ 为偶数},\ u\equiv1\pmod3.
\end{cases}
\]

证明：由完成平方转成 y²≡D mod 3^R。R≤t 时 y 必须被 3^{ceil(R/2)} 整除。R>t 时根必须有赋值 t/2，因此 t 必须为偶数；除去 3^t 后，单位平方根存在当且仅当 u≡1 mod3。两个单位根逐层唯一提升，每个对应 3^{t/2} 个原变量剩余类。

特别地，h=2 的根密度是 3^{−ceil(R/2)}；固定的非退化 h 若有高层根，其根密度最终是常数倍 3^{−R}。这是二重根带来的局部计数差异，不是素数对下界。

## 6. 相反等层的完整间距深度规律

设 1<p<q 为奇整数，F₃(p)=k>0、F₃(q)=−k。记

\[
\delta=q-p-2\ge0,\quad s=F_3(pq),\quad p+1=3^k a.
\]

若 δ=0，则 s=2k。若 δ>0，令 t=v₃(δ)。由 q−1 与 p+1 都被 3^k 整除，t≥k。又

\[
pq+1=(p+1)^2+p\delta.
\]

因此当 t≠2k 时

\[
s=\min(2k,t).
\]

当 t=2k，写 δ=3^{2k}u，则

\[
pq+1=3^{2k}(a^2-u+3^k au).
\]

a 是 3-进单位，故 a²≡1 mod3。因此

\[
s>2k\iff u\equiv1\pmod3,
\quad s=2k\iff u\equiv2\pmod3.
\]

由此得到

\[
s\ge2k\iff 3^{2k}\mid\delta.
\]

因为 δ 为偶数，可以写 δ=2·3^{2k}r₀。进一步

\[
s>2k\iff r_0\equiv2\pmod3.
\]

所以乘积深度严格超过 2k 时，两数反而不可能为孪生，且

\[
q-p\ge2+4\cdot3^{2k}.
\]

这不是素数对存在性结果。它也说明不能把“乘积深度越高”误读为“越接近孪生”。

## 7. 本原特征与 Kloosterman 谱接口

令 Q=3^{2r}。由 Dirichlet 特征正交性，对 3∤ab，

\[
\boxed{
W_r(ab+1)=\frac3{\varphi(Q)}
\sum_{\substack{\chi\bmod Q\\\operatorname{cond}(\chi)=Q}}
\chi(-1)\chi(a)\chi(b).
}
\]

证明：分别展开模 Q 和 Q/3 的剩余类指标。因 φ(Q)=3φ(Q/3)，来自 Q/3 的全部低导数特征恰好相消，留下导数恰为 Q 的特征。本公式是标准有限群正交性的应用，不把“本原谱”当成已经得到抵消的证据。

另记 e_Q(t)=exp(2πit/Q)。根计数的离散 Fourier 变换有

\[
\sum_{h\bmod Q}R_{2r}(h)e_Q(ah)
=\sum_{u\bmod Q}^{*}e_Q\bigl(-a(u+u^{-1})\bigr).
\]

因为每个单位 u 对应唯一位移 h=−u−u^{-1}。右侧是经典 Kloosterman 和。对 3∤a，分块展开得到

\[
\sum_{u\bmod3^{2r}}^{*}e_{3^{2r}}\bigl(-a(u+u^{-1})\bigr)
=3^r\{e_{3^{2r}}(-2a)+e_{3^{2r}}(2a)\}.
\]

其驻点为 u=±1，临界值为 ±2。这是局部二次切触、根计数异常与指数和的同一个机制。

## 8. 有限 CRT 分解：为什么局部公式不能直接解决素性

若 d 是与 3 互素的平方自由正整数，记

\[
\nu_\ell(h)=\begin{cases}1,&\ell\mid h,\\2,&\ell\nmid h.\end{cases}
\]

则中国剩余定理给出精确计数

\[
\#\{n\bmod3^R d:3^R\mid n(n+h)+1,\ (n(n+h),d)=1\}
=R_R(h)\prod_{\ell\mid d}(\ell-\nu_\ell(h)).
\]

因此这个局部过滤对其他互素小素数的筛除，在均匀剩余类模型里仍然完全分解。它没有自动获取 Liouville 符号或两端素性的控制。这个有限分解不能被扩大成“任何 F₃ 方法都不可能有用”的断言。

## 9. 素数权实验与精确的剩余问题

固定 r=3、H=240，定义

\[
S(X)=\sum_{\substack{2\le h\le240\\h\text{ 偶}}}
\sum_{\substack{5\le p\le X\\p,p+h\text{ 素数}}}
W_3(p(p+h)+1).
\]

此处 W₃ 的下标是 r=3，不是另一种赋值底数。

令 E(X) 是同一和中 h≠2 的部分；令 T_{≥3}(X) 计数满足 F₃(p)≥3 的孪生对。则逐项恒等地

\[
S(X)=2T_{\ge3}(X)+E(X).
\]

实验口径：5≤p≤X，允许 p+h>X；两个端点都由普通 Eratosthenes 筛检测素性。结果：

| X | h=2 的贡献 2T_{≥3} | 其他间距贡献 E | 总和 S |
|---:|---:|---:|---:|
| 100,000 | 266 | 4 | 270 |
| 1,000,000 | 1,846 | 36 | 1,882 |
| 10,000,000 | 13,072 | 98 | 13,170 |

这些数值表明本次有限样本中其他间距贡献存在明显抵消，但不证明 E=o(X/log²X)，更不证明任何形式的孪生素数无穷性。

一个明确的分析任务是独立估计 E，研究能否获得素数权下的提升差分抵消。即便证明 E=o(X/log²X)，仍需另一个真正的正下界，例如 S≥cX/log²X（c>0），才可推出无穷多个这一层尾中的孪生对。不得把 S 的正下界当成自动成立；这两个任务目前均未解决。

进一步可研究 r=r(X)、H=H(X)<3^{2r−1}−2 的一致估计，使位移平均增长。但这需要给出明确参数范围和误差，不能直接从固定模周期公式交换到素数平均。

## 10. 本轮计算核验范围

- 根计数：5,648 组同余计数，枚举 18,756,976 个剩余类，全部吻合。
- 等层间距公式：检查 3≤p<q≤2001 的 499,500 对奇整数，其中 27,896 对符合相反等层假设；所有相应结论吻合。
- 一般二次传递公式：2,022 组二次多项式，枚举 2,966,022 个剩余类，全部吻合；包括底数 3、5、7。
- CRT 分解：48 组计数，枚举 22,560 个剩余类，全部吻合。
- 素数实验：X=10⁵、10⁶、10⁷；这是数据，不是无限证明。

脚本只依赖 Python 标准库。

## 11. 已有工作与新颖性边界

当前读取的仓库源码 `OmegaBalance/F3SumProduct.lean` 已包含孪生乘积加倍及附加乘积深度下的间距格点；本轮没有把这些结果重新计为新增形式化。本轮不修改仓库。

二次同余、Hensel 提升、本原 Dirichlet 特征投影、素数幂模的 Kloosterman 和都是成熟理论。上述具体组合是本轮为 F₃ 推导的研究接口，不据此声称首次发现或已达到论文主定理的新颖性标准。真正更有分量的候选是新的素数权抵消估计，而不是再次命名局部公式。

参考资料：

1. Keith Conrad, *Hensel’s Lemma*, §§2–3. https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf
2. R. A. Cowan, D. J. Katz, L. M. White, *A New Generating Function for Calculating the Igusa Local Zeta Function*, arXiv:1506.07869. https://arxiv.org/abs/1506.07869
3. G. Ricotta, E. Royer, I. Shparlinski, *Kloosterman paths of prime powers moduli, II*, arXiv:1810.01150. https://arxiv.org/abs/1810.01150
4. Terence Tao, *Open question: The parity problem in sieve theory* (2007). https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/
5. 已读取的仓库源码： https://github.com/UyNewNas/omega-balance-prime-lean/blob/master/OmegaBalance/F3SumProduct.lean

# F3-HIER：完整书面证明

状态：\`PAPER-AUDITED\`。精确定理见 [theorem.md](theorem.md)。

## 1. 幂赋值公式

### 引理 1.1

设 \(n>1\)、\(F_3(n)=k\ge1\)，且 \(u\ge1\)。则
\[
v_3\bigl(n^u-(-1)^u\bigr)=k+v_3(u),
\tag{1.1}
\]
并且
\[
F_3(n^u)=(-1)^{u+1}\bigl(k+v_3(u)\bigr).
\tag{1.2}
\]

### 证明

因为 \(F_3(n)=k>0\)，所以
\[
v_3(n+1)=k,\qquad v_3(n-1)=0.
\]
令
\[
U=-n.
\]
则
\[
U\equiv1\pmod3,\qquad v_3(U-1)=k.
\]

写
\[
u=3^t a,\qquad 3\nmid a.
\]
先看三次幂提升。若 \(V\equiv1\pmod3\)，则
\[
V^3-1=(V-1)(V^2+V+1).
\]
写 \(V=1+3^rz\)，其中 \(r\ge1\)、\(3\nmid z\)，则
\[
V^2+V+1
=
3+3^{r+1}z+3^{2r}z^2
=
3\bigl(1+3^rz+3^{2r-1}z^2\bigr),
\]
括号为三进单位，所以
\[
v_3(V^3-1)=v_3(V-1)+1.
\]
迭代 \(t\) 次得
\[
v_3(U^{3^t}-1)=k+t.
\]

再利用 \(3\nmid a\)：
\[
\frac{X^a-1}{X-1}=1+X+\cdots+X^{a-1}\equiv a\not\equiv0\pmod3
\]
当 \(X\equiv1\pmod3\)。因此
\[
v_3(U^u-1)=v_3(U^{3^t}-1)=k+t=k+v_3(u).
\]
由于
\[
U^u=(-1)^u n^u,
\]
即得 (1.1)。

若 \(u\) 为奇数，则 \(n^u\equiv-1\pmod3\)，所以
\[
v_3(n^u+1)=k+v_3(u),\qquad v_3(n^u-1)=0.
\]
若 \(u\) 为偶数则恰好相反。于是 (1.2) 成立。 \(\square\)

---

## 2. 低次数单项式刚性

固定
\[
q=3^s,\qquad M=3^{k+s}.
\]
设
\[
p_i\equiv n\pmod M
\]
对所有 \(i\) 成立。

考虑任意非空单项式
\[
P=\prod_i p_i^{e_i},
\qquad
u=\sum_i e_i.
\]
若
\[
1\le u<q,
\]
则
\[
P\equiv n^u\pmod M.
\tag{2.1}
\]

由 \(u<3^s\) 得
\[
v_3(u)\le s-1,
\]
所以引理 1.1 给出
\[
v_3\bigl(n^u-(-1)^u\bigr)
=
k+v_3(u)
<
k+s.
\tag{2.2}
\]
因此模 \(3^{k+s}\) 的同余已经足以固定这个精确赋值。

由 (2.1)–(2.2)，
\[
v_3\bigl(P-(-1)^u\bigr)
=
k+v_3(u).
\tag{2.3}
\]
另一方面 \(P\equiv(-1)^u\pmod3\)，所以另一侧邻数不被 \(3\) 整除。

故
\[
\boxed{
F_3(P)=(-1)^{u+1}\bigl(k+v_3(u)\bigr)
}
\qquad(1\le u<q).
\tag{2.4}
\]

这一步允许任意重复因子，只使用总次数 \(u\)。

### 九端点计数

当 \(q=9\) 时，非空真子集数为
\[
2^9-2=510.
\]
九变量总次数 \(1\) 到 \(8\) 的单项式个数为
\[
\sum_{u=1}^8\binom{u+8}{8}
=
\binom{17}{8}-1
=
24309.
\]
它们全部由 (2.4) 固定。

---

## 3. 第一次共振发生在次数 \(q=3^s\)

次数 \(u<q\) 时，
\[
k+v_3(u)\le k+s-1.
\]
而当
\[
u=q=3^s
\]
时，
\[
k+v_3(q)=k+s.
\]
这正好撞到模数
\[
M=3^{k+s}
\]
的精度边界。

因此“所有次数小于 \(q\) 的数据刚性、次数 \(q\) 首次出现自由度”不是偶然现象，而是由
\[
v_3(u)<s\quad(u<3^s)
\]
与
\[
v_3(3^s)=s
\]
直接造成的。

---

## 4. 总乘积的系数和判据

令现在恰好有 \(q\) 个端点
\[
p_i=n+MWc_i d,
\qquad
i=0,\ldots,q-1,
\]
其中
\[
3\nmid W.
\]
记
\[
C=\sum_i c_i.
\]

由引理 1.1 对 \(u=q\) 应用，
\[
v_3(n^q+1)=k+s.
\]
所以
\[
A(n):=\frac{n^q+1}{M}
\]
是整数且为三进单位。

展开总乘积：
\[
\prod_i(n+MWc_i d).
\]
零次项是 \(n^q\)。一次项为
\[
MW\left(\sum_i c_i\right)n^{q-1}d
=
MWCn^{q-1}d.
\]
所有二次及以上项至少含 \(M^2\)。

因此存在整数多项式 \(H_n(d)\)，使
\[
\prod_i p_i+1
=
M G_n(d),
\tag{4.1}
\]
其中
\[
\boxed{
G_n(d)=A(n)+WCn^{q-1}d+M H_n(d).
}
\tag{4.2}
\]

因为 \(q\) 为奇数且每个 \(p_i\equiv n\equiv-1\pmod3\)，有
\[
\prod_i p_i\equiv-1\pmod3.
\]
所以
\[
v_3\left(\prod_i p_i-1\right)=0,
\]
从而
\[
F_3\left(\prod_i p_i\right)
=
k+s+v_3(G_n(d)).
\tag{4.3}
\]

### 情形 A：\(3\mid C\)

模 \(3\) 下
\[
G_n(d)\equiv A(n)\not\equiv0\pmod3.
\]
所以
\[
v_3(G_n(d))=0
\]
对所有 \(d\) 恒成立。因此
\[
\boxed{
F_3\left(\prod_i p_i\right)=k+s.
}
\tag{4.4}
\]

### 情形 B：\(3\nmid C\)

因为 \(q-1\) 为偶数、\(n\equiv-1\pmod3\)，有
\[
n^{q-1}\equiv1\pmod3.
\]
于是
\[
G_n(d)\equiv A(n)+WCd\pmod3,
\tag{4.5}
\]
且
\[
G_n'(d)\equiv WC\not\equiv0\pmod3.
\tag{4.6}
\]

所以模 \(3\) 有唯一根，而且该根非零。

更强地，对任意 \(d,e\in\mathbb Z_3\)，由 (4.2)
\[
G_n(d)-G_n(e)
=
(d-e)\left(
WCn^{q-1}+M K_n(d,e)
\right)
\tag{4.7}
\]
其中 \(K_n\in\mathbb Z[d,e]\)。

括号模 \(3\) 同余于 \(WC\)，是单位，因此
\[
\boxed{
v_3(G_n(d)-G_n(e))=v_3(d-e).
}
\tag{4.8}
\]

这说明 \(G_n\) 是 \(\mathbb Z_3\) 上的等距映射。

另一方面，对任意 \(T\ge1\)，若已知模 \(3^T\) 的某个原像，提升到模 \(3^{T+1}\) 时，由导数为单位可知三个候选中恰有一个命中给定目标。因此
\[
G_n:\mathbb Z/3^T\mathbb Z\to\mathbb Z/3^T\mathbb Z
\]
对每个 \(T\) 都是双射。

逆极限给出
\[
G_n:\mathbb Z_3\to\mathbb Z_3
\]
为双射。因此存在唯一
\[
d_*(n)\in\mathbb Z_3
\]
使
\[
G_n(d_*)=0.
\]
由 (4.5) 根模 \(3\) 非零，故
\[
d_*(n)\in\mathbb Z_3^\times.
\]

把 \(e=d_*(n)\) 代入 (4.8)，得到
\[
v_3(G_n(d))
=
v_3(d-d_*(n)).
\]
结合 (4.3)：
\[
\boxed{
F_3\left(\prod_i p_i\right)
=
k+s+v_3(d-d_*(n)).
}
\tag{4.9}
\]

---

## 5. “末点移动一格”打开根分支

普通系数
\[
c_i=i,\qquad0\le i<q
\]
的总和是
\[
C_{\rm ord}
=
\frac{q(q-1)}2.
\]
因为 \(3\mid q\)，
\[
C_{\rm ord}\equiv0\pmod3.
\]
所以总乘积深度由 (4.4) 锁死在
\[
k+s.
\]

现在把最后一个系数从 \(q-1\) 改成 \(q\)。新系数和
\[
C_{\rm mov}
=
\frac{q(q-1)}2+1
\equiv1\pmod3.
\]
于是进入 (4.9) 的唯一根分支。

但所有端点仍满足
\[
p_i\equiv n\pmod M,
\]
所以第 2 节的全部总次数小于 \(q\) 的单项式数据完全不变。

这证明了确定性的“锁死/开放”对照。

---

## 6. 主形状的局部可容许性

现在选择
\[
W=
\prod_{\substack{\ell\le q\\\ell\ {\rm prime},\ \ell\ne3}}\ell
\]
并采用末点移动系数
\[
(c_i)=(0,1,\ldots,q-2,q).
\]

需要同时为素数的形式是
\[
d,\quad p_0,\ldots,p_{q-1}.
\]

固定一个足够高的三进参数类
\[
(n,d)\equiv(a_0,b_0)\pmod{Q},
\qquad Q=3^A,
\]
使
\[
F_3(n)=k,\qquad3\nmid d.
\]
写
\[
n=a_0+Qx,\qquad d=b_0+Qy.
\]
各形式的齐次方向为
\[
(0,1),\qquad(1,h_i),
\]
其中
\[
h_i=MWc_i.
\]
因为 \(c_i\) 严格递增，方向两两不成比例，所以系统有限复杂。

### 素数 \(3\)

固定参数类已经保证
\[
d\not\equiv0\pmod3,\qquad
p_i\equiv n\equiv-1\pmod3.
\]
故局部因子
\[
\beta_3=\left(\frac32\right)^{q+1}.
\tag{6.1}
\]

### 小素数 \(\ell\le q\)、\(\ell\ne3\)

因为 \(\ell\mid W\)，
\[
h_i\equiv0\pmod\ell
\]
对所有 \(i\) 成立。

因此只需
\[
d\ne0,\qquad n\ne0\pmod\ell.
\]
允许参数数为
\[
(\ell-1)^2.
\]
局部因子为
\[
\frac{(\ell-1)^2}{\ell^2}
\left(\frac{\ell}{\ell-1}\right)^{q+1}
=
\left(\frac{\ell}{\ell-1}\right)^{q-1}.
\tag{6.2}
\]

### 大素数 \(\ell>q\)

此时 \(\ell\nmid MW\)，且 \(c_i\) 模 \(\ell\) 两两不同，因为它们之间非零差的绝对值都不超过 \(q<\ell\)。

要求 \(d\ne0\) 后，令
\[
r=n/d.
\]
端点素性局部条件要求 \(r\) 避开
\[
-h_i,\qquad i=0,\ldots,q-1,
\]
共 \(q\) 个不同类。

所以允许参数数为
\[
(\ell-1)(\ell-q).
\]
局部因子为
\[
\beta_\ell
=
\frac{(\ell-1)(\ell-q)}{\ell^2}
\left(\frac{\ell}{\ell-1}\right)^{q+1}
=
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}.
\tag{6.3}
\]

对固定 \(q\)，
\[
\beta_\ell
=
\frac{1-q/\ell}{(1-1/\ell)^q}
=
1+O_q(\ell^{-2}).
\tag{6.4}
\]
因此大素数尾部乘积收敛到非零正数。

于是奇异乘积为
\[
\boxed{
\mathfrak S_q
=
\left(\frac32\right)^{q+1}
\prod_{\substack{\ell\le q\\\ell\ne3}}
\left(\frac{\ell}{\ell-1}\right)^{q-1}
\prod_{\ell>q}
\frac{\ell^{q-1}(\ell-q)}{(\ell-1)^q}
>0.
}
\tag{6.5}
\]

---

## 7. 固定三进参数类的素数计数

对固定模数 \(Q=3^A\) 的允许类，原盒
\[
X<n,d\le2X
\]
对应 \((x,y)\) 平面中面积
\[
\frac{X^2}{Q^2}+O(X)
\]
的凸矩形。

所有形式为固定非退化仿射线性形式。由完整的有限复杂度线性形式素数定理，
\[
\#\{\text{该固定类中的全素数参数}\}
=
\left(
\frac{\mathfrak S_q}{Q^2}
+o_{k,s,Q}(1)
\right)
\frac{X^2}{(\log X)^{q+1}}.
\tag{7.1}
\]

这里的主系数不依赖允许三进参数类的具体代表。

模 \(Q\) 下满足
\[
v_3(n+1)=k
\]
的 \(n\) 类有
\[
2\cdot3^{A-k-1}
\]
个，而单位 \(d\) 类有
\[
2\cdot3^{A-1}
\]
个。

总类数为
\[
4\cdot3^{2A-k-2}.
\tag{7.2}
\]

将 (7.1) 求和，得到
\[
|\mathcal Q_{k,s}(X)|
=
\left(
\frac4{3^{k+2}}\mathfrak S_q+o(1)
\right)
\frac{X^2}{(\log X)^{q+1}}.
\]
因此
\[
\boxed{
\kappa_{k,s}
=
\frac4{3^{k+2}}\mathfrak S_q.
}
\tag{7.3}
\]

这就是 theorem.md 中的显式常数。

---

## 8. 精确总深度的几何分布

固定 \(n\) 的允许三进类。

由第 4 节，主形状中的 \(G_n\) 对所有 \(3^T\) 有唯一单位根类。

模 \(3^T\) 的单位数为
\[
2\cdot3^{T-1}.
\]
其中一半不落入模 \(3\) 的根类，因此
\[
\Pr(v_3(G_n(d))=0)=\frac12.
\tag{8.1}
\]

对 \(t\ge1\)，满足
\[
v_3(G_n(d))\ge t
\]
的单位类比例为
\[
\frac1{2\cdot3^{t-1}}.
\]
所以精确等于 \(t\) 的比例为
\[
\frac1{2\cdot3^{t-1}}
-
\frac1{2\cdot3^t}
=
3^{-t}.
\tag{8.2}
\]

令
\[
b=k+s.
\]
由
\[
D=b+v_3(G_n(d))
\]
得到
\[
w_b(R)
=
\begin{cases}
1/2,&R=b,\\
3^{-(R-b)},&R>b.
\end{cases}
\tag{8.3}
\]

判定固定 \(R\) 只需取足够高但固定的模 \(3^A\)。每个允许参数类具有相同素数主系数，所以将有限类比例乘入 (7.1) 即得
\[
\#\{D=R\}
=
\left(
\kappa_{k,s}w_b(R)+o(1)
\right)
\frac{X^2}{(\log X)^{q+1}}.
\]

每个 \(w_b(R)>0\)，故每个固定 \(R\ge b\) 都有无穷多全素数实现。

---

## 9. 普通族与末点移动族具有相同素数主项

普通族系数
\[
(0,1,\ldots,q-1)
\]
与移动族
\[
(0,1,\ldots,q-2,q)
\]
在每个素数处排除的剩余类数量完全相同。

- 对 \(\ell\le q,\ell\ne3\)，因为 \(\ell\mid W\)，全部偏移都归零，所以两者都有 \(\nu_\ell=1\)。
- 对 \(\ell>q\)，两组各自都有 \(q\) 个互不相同的系数类，所以两者都有 \(\nu_\ell=q\)。
- 模 \(3\) 的单位条件也相同。

因此奇异乘积完全相同，三进允许类数量也相同，所以
\[
B_{\rm ordinary}(X)
\sim
B_{\rm moved}(X)
\sim
\kappa_{k,s}\frac{X^2}{(\log X)^{q+1}}.
\tag{9.1}
\]

但第 5 节已经证明：
\[
D_{\rm ordinary}\equiv k+s,
\]
而移动族有 (8.3) 的无限几何尾。

这给出了“相同全部低次数数据 + 相同素数计数主系数，但最高阶深度分布不同”的严格对照。

---

## 10. 不存在统一有限次数截断

给定固定 \(L\)，选择
\[
s\quad\text{使}\quad3^s>L.
\]
那么 F3-HIER-1 的所有总次数
\[
1\le u\le L
\]
单项式 \(F_3\) 数据全部固定，而总乘积深度遍历所有
\[
R\ge k+s.
\]
所以任何固定的有限次数上限都不足以作为所有更高阶总乘积深度的充分坐标。

注意这只是否定“仅保留这些 \(F_3\) 数值”的统一截断，不是否定完整整数输入、完整三进单位坐标或根坐标的恢复能力。

---

## 11. 数值 sanity check

研究轮对
\[
k=1,\quad s=2
\]
的九端点形状搜索得到 60 组十素数配置；总乘积深度 \(3,4,5,6\) 的数量分别为
\[
30,\ 21,\ 8,\ 1.
\]

其中
\[
n=147083,\qquad d=43
\]
给出九个素数端点
\[
147083,\ 228353,\ 309623,\ 390893,\ 472163,\ 553433,\ 634703,\ 715973,\ 878513
\]
且总乘积深度为 \(6\)。

有限搜索只用于排错；无限结论来自第 7–8 节。

---

## 12. 外部输入与范围

F3-HIER 的局部算术部分——幂赋值、低次数刚性、系数和判据、等距根坐标和有限剩余类比例——均在本文内部证明。

全素数渐近使用外部有限复杂度素数线性形式理论：

- \(q=3\) 时系统复杂度至多 \(2\)，Green–Tao 2010 已无条件覆盖；
- 一般固定 \(q\) 使用后续 Green–Tao / Green–Tao–Ziegler 完成的有限复杂度版本。

固定 \(d\) 后系统退化为一维仿射相关形式，本文的素数计数工具不再适用。

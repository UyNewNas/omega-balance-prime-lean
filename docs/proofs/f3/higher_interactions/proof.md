# F3-HI：完整书面证明

状态：`PAPER-AUDITED`。精确陈述见 [theorem.md](theorem.md)。

## 1. 六个低阶值的确定性锁定

固定 (kge1)，令
[
M=3^{k+1},
qquad
p_0=n,quad p_1=n+2Md,quad p_2=n+6Md.
]

假设
[
n>1,qquad d>0,qquad 3
mid d,qquad F_3(n)=k.
]
因为 (k>0)，必有
[
v_3(n+1)=k,qquad v_3(n-1)=0.
]
因此可写成
[
n=-1+3^k a,qquad 3
mid a.
	ag{1.1}
]

### 引理 1.1：三个单点值全部为 (k)

由于
[
p_iequiv npmod{3^{k+1}},
]
有
[
p_i+1equiv 3^k apmod{3^{k+1}},
qquad
p_i-1equiv -2pmod3.
]
故
[
v_3(p_i+1)=k,qquad v_3(p_i-1)=0,
]
从而
[
oxed{F_3(p_i)=kqquad(i=0,1,2).}
	ag{1.2}
]

### 引理 1.2：三个两两乘积值全部为 (-k)

对任意 (i
e j)，
[
p_i p_jequiv n^2pmod{3^{k+1}}.
]
由 (1.1)
[
n^2-1
=
-2cdot3^k a+3^{2k}a^2
equiv
-2cdot3^k a
pmod{3^{k+1}},
]
这里使用 (2kge k+1)。由于 (3
mid2a)，
[
v_3(p_i p_j-1)=k.
]
另一方面 (p_i p_jequiv1pmod3)，故
[
v_3(p_i p_j+1)=0.
]
所以
[
oxed{F_3(p_i p_j)=-k.}
	ag{1.3}
]

至此三个单点与三个两两乘积共六个值已经完全锁定，而且尚未使用素数性。

## 2. 三因子乘积的剩余自由度

定义
[
A(n)=rac{n^3+1}{M}.
]
由 (1.1) 直接展开：
[
n^3+1
=
3^{k+1}a-3^{2k+1}a^2+3^{3k}a^3,
]
故
[
A(n)
=
a-3^k a^2+3^{2k-1}a^3inmathbb Z,
qquad
A(n)equiv apmod3.
	ag{2.1}
]

再展开三因子乘积：
[
egin{aligned}
p_0p_1p_2+1
&=
n(n+2Md)(n+6Md)+1\
&=
n^3+1+8Mn^2d+12M^2nd^2\
&=
M,G_n(d),
end{aligned}
]
其中
[
oxed{
G_n(d)=A(n)+8n^2d+12Mnd^2.
}
	ag{2.2}
]

三个因子均模 (3) 同余于 (-1)，故
[
p_0p_1p_2equiv-1pmod3,
]
从而
[
v_3(p_0p_1p_2-1)=0.
]
于是
[
oxed{
D(n,d)=F_3(p_0p_1p_2)
=
k+1+v_3(G_n(d)).
}
	ag{2.3}
]

这说明六个低阶值没有记录的信息恰好进入了余因子 (G_n(d))。

## 3. (G_n(d)) 的唯一简单三进根

模 (3) 看，由 (n^2equiv1pmod3) 和 (2.1) 得
[
G_n(d)equiv a+2dpmod3.
]
因此唯一根为
[
dequiv apmod3.
	ag{3.1}
]
该根是单位。

同时
[
G_n'(d)=8n^2+24Mndequiv2pmod3,
	ag{3.2}
]
所以导数始终是三进单位。

### 引理 3.1：唯一根逐层唯一提升

若 (u) 是模 (3^t) 的根，则对 (bin{0,1,2})
[
G_n(u+3^t b)
equiv
G_n(u)+3^t bG_n'(u)
pmod{3^{t+1}}.
]
除以 (3^t) 后，由 (G_n'(u)
otequiv0pmod3)，恰有一个 (bmod3) 使右侧继续为 (0pmod3)。

因此对每个 (tge1)，模 (3^t) 恰有一个单位根。

### 引理 3.2：有限层级的精确比例

在模 (3^T) 的单位剩余类中均匀计数。单位总数为
[
2cdot3^{T-1}.
]
对 (1le tle T)，满足
[
3^tmid G_n(d)
]
的单位类数为
[
3^{T-t},
]
故
[
Pr(v_3(G_n(d))ge t)
=
rac{1}{2cdot3^{t-1}}.
	ag{3.3}
]
于是
[
Pr(v_3(G_n(d))=0)=rac12,
	ag{3.4}
]
且对 (1le t<T)
[
Pr(v_3(G_n(d))=t)
=
rac1{2cdot3^{t-1}}
-
rac1{2cdot3^t}
=
3^{-t}.
	ag{3.5}
]

结合 (2.3)，局部深度分布就是
[
Pr(D=k+1)=rac12,
qquad
Pr(D=k+1+t)=3^{-t}quad(tge1).
	ag{3.6}
]

注意这里是有限剩余类的精确计数，不是把素数事件视为独立随机事件。

## 4. 四个素数形式与局部因子

现在进入全素数计数。

固定 (Age k+1)、(Q=3^A)，并固定一个参数剩余类
[
(n,d)equiv(b,c)pmod Q
]
满足
[
F_3(b)=k	ext{ 在该模类上稳定},qquad 3
mid c.
]

写
[
n=b+Qx,qquad d=c+Qy.
]
四个需要同时为素数的仿射线性形式为
[
psi_0=d,quad
psi_1=n,quad
psi_2=n+2Md,quad
psi_3=n+6Md.
]
其齐次方向分别为
[
(0,1),quad(1,0),quad(1,2M),quad(1,6M).
]
两两不成比例。对四个形式中的任意一个，把其余三个各自作为一个单元素组，即得 Green–Tao 意义下复杂度至多 (2)。

### 素数 (3)

固定参数类已经保证四个形式都不被 (3) 整除，因此
[
eta_3=(3/2)^4.
	ag{4.1}
]

### 素数 (2)

因为 (M) 为奇数，模 (2) 时
[
n+2Mdequiv n,qquad n+6Mdequiv n.
]
四个形式同时为单位当且仅当
[
(n,d)equiv(1,1)pmod2.
]
所以
[
eta_2=rac14cdot2^4=4.
	ag{4.2}
]

### 素数 (ellge5)

参数变换模 (ell) 可逆。先要求 (d
otequiv0pmodell)，然后令 (r=n/d)。需要避开
[
requiv0, -2M, -6Mpmodell.
]
这三个类互异，因为它们的非零差只含素因子 (2,3)。因此合格参数数为
[
(ell-1)(ell-3),
]
相应局部因子为
[
eta_ell
=
rac{(ell-1)(ell-3)}{ell^2}
left(rac{ell}{ell-1}ight)^4
=
rac{ell^2(ell-3)}{(ell-1)^3}.
	ag{4.3}
]
并且
[
eta_ell
=
1-rac{3ell-1}{(ell-1)^3}
=
1+O(ell^{-2}).
]
所以
[
mathfrak C
=
prod_{ellge5}eta_ell
]
绝对收敛意义下给出严格正的无穷乘积，而完整奇异级数为
[
mathfrak S
=
eta_2eta_3mathfrak C
=
rac{81}{4}mathfrak C.
	ag{4.4}
]

## 5. 每个固定三进参数类的素数计数

在原盒
[
X<n,dle2X
]
中，固定模 (Q) 参数类对应于 ((x,y)) 平面中的一个边长为 (X/Q+O(1)) 的矩形，其面积为
[
rac{X^2}{Q^2}+O(X).
	ag{5.1}
]
四形式在该区域内均为正且与 (X) 同阶。

由 Green–Tao 的复杂度至多 (2) 素数线性形式定理，得到
[
#{
(n,d)	ext{ 属于该固定模 }Q	ext{ 类且四形式均为素数}
}
=
left(
rac{mathfrak S}{Q^2}+o_{k,Q}(1)
ight)
rac{X^2}{(log X)^4}.
	ag{5.2}
]
主系数与允许剩余类的具体代表无关：除 (ell=3) 外参数平移缩放模 (ell) 可逆；在 (ell=3) 处所有允许类都使四形式为单位。

## 6. 汇总得到 (mathcal Q_k(X)) 的主项

模 (Q=3^A) 下，满足
[
v_3(n+1)=k
]
的 (n) 类数为
[
2cdot3^{A-k-1}.
	ag{6.1}
]
单位 (d) 类数为
[
2cdot3^{A-1}.
	ag{6.2}
]
故允许参数类总数为
[
4cdot3^{2A-k-2}.
	ag{6.3}
]

把 (5.2) 对这些有限个类求和：
[
egin{aligned}
|mathcal Q_k(X)|
&=
left(
4cdot3^{2A-k-2}
cdot
rac1{3^{2A}}
cdot
rac{81}{4}mathfrak C
+o_k(1)
ight)
rac{X^2}{(log X)^4}\
&=
left(
3^{2-k}mathfrak C+o_k(1)
ight)
rac{X^2}{(log X)^4}.
end{aligned}
]
即
[
oxed{
|mathcal Q_k(X)|
=
(kappa_k+o_k(1))
rac{X^2}{(log X)^4}.
}
	ag{6.4}
]

## 7. 精确深度 (D=R) 的主项

固定 (Rge k+1)，取
[
Age R+1.
]
此时模 (3^A) 已足够决定
[
v_3(G_n(d))
]
是否等于 (R-k-1)：因为 (A(n)=(n^3+1)/3^{k+1})，把 (n) 固定到模 (3^A) 后，(A(n)) 至少确定到模 (3^{A-k-1})，而 (Age R+1) 正好覆盖判定所需精度。

对每个固定允许 (n) 类，引理 3.2 给出完全相同的 (d) 类比例：
[
w_k(R)=
egin{cases}
1/2,&R=k+1,\
3^{-(R-k-1)},&Rge k+2.
end{cases}
]
由于 (5.2) 对每个允许模类具有相同主系数，把对应的事件类求和即得
[
oxed{
#{(n,d)inmathcal Q_k(X):D(n,d)=R}
=
(kappa_k w_k(R)+o_{k,R}(1))
rac{X^2}{(log X)^4}.
}
	ag{7.1}
]

每个 (w_k(R)>0)，所以右侧趋于无穷。由此 F3-HI-1 与 F3-HI-2 得证。

## 8. (k=1) 的固定形状

当 (k=1) 时
[
M=9,qquad
(p_0,p_1,p_2)=(n,n+18d,n+54d).
]
因此对每个 (Rge2)，有无穷多个素数
[
d,n,n+18d,n+54d
]
满足
[
(F_3(p_0),F_3(p_1),F_3(p_2))=(1,1,1),
]
[
(F_3(p_0p_1),F_3(p_0p_2),F_3(p_1p_2))=(-1,-1,-1),
]
而
[
F_3(p_0p_1p_2)=R.
]

这里偏移 (18,54) 完全不随 (R) 改变。

## 9. 有限剩余模式的素数伸缩实现

现在证明 F3-HI-3。

固定 (sge2)、(Q=3^A)，给定单位类
[
a_0,ldots,a_{s-1},bpmod Q.
]
令
[
P=
prod_{substack{ellle s\ ell	ext{ prime}, ell
e3}}
ell.
]
对每个 (ige1)，用中国剩余定理选取 (h_i) 使
[
h_iequiv(a_i-a_0)b^{-1}pmod Q,
qquad
h_iequiv0pmod P.
	ag{9.1}
]
再逐次加上 (QP) 的倍数，使
[
0=h_0<h_1<cdots<h_{s-1}.
	ag{9.2}
]

若
[
nequiv a_0,qquad dequiv bpmod Q,
]
则
[
n+h_i dequiv a_ipmod Q.
	ag{9.3}
]

考虑 (s+1) 个形式
[
d,quad n+h_0d,ldots,n+h_{s-1}d.
]
其方向为
[
(0,1),quad(1,h_0),ldots,(1,h_{s-1}),
]
两两不成比例，因此是有限复杂度系统。

检查局部障碍。模 (3) 时所有形式都是预先指定的单位。对 (ell
e3)，要求 (d
e0) 后，比例 (n/d) 需要避开
[
-h_ipmodell.
]
令
[

u_ell=|{h_imodell}|.
]
若 (ellle s)，则由 (9.1) 有 (
u_ell=1<ell)；若 (ell>s)，则
[

u_ellle s<ell.
]
所以每个局部因子都严格为正。

除去整除某个 (h_i-h_j) 的有限个素数后，
[

u_ell=s,
]
此时局部因子为
[
rac{ell^{s-1}(ell-s)}{(ell-1)^s}
=
1+O_s(ell^{-2}).
]
故奇异乘积收敛到正数。

应用一般有限复杂度线性形式素数定理，即得某个 (c>0) 使参数对数为
[
(c+o(1))
rac{X^2}{(log X)^{s+1}}.
	ag{9.4}
]
这证明 F3-HI-3。

## 10. 从剩余模式到有限单项式 (F_3) 模式

设正整数 (x_i) 实现有限组目标
[
F_3!left(prod_i x_i^{e_{alpha,i}}ight)
=
f_alpha
e0.
]
因为每个相关乘积都是三进单位，正负两侧中恰有一侧的 (v_3) 为 (|f_alpha|)，另一侧为 (0)。

取
[
A>max_alpha |f_alpha|.
]
若
[
p_iequiv x_ipmod{3^A},
]
则每个单项式乘积也在模 (3^A) 下与原乘积同余。由于相关精确赋值都严格小于 (A)，同余稳定性保证所有目标 (F_3) 值保持不变。

现在对
[
a_iequiv x_ipmod{3^A}
]
应用 F3-HI-3，即得到无穷多全素数伸缩实现，且步长 (d) 也为素数。

## 11. 固定步长不在本证明范围内

若固定 (d=D)，则
[
n,quad n+2MD,quad n+6MD
]
变成单变量仿射形式，其齐次部分彼此成比例，属于无限复杂度情形。上面的 Green–Tao 有限复杂度定理不能应用。

因此本结果是“两参数固定形状”的无穷素数配置定理，不是固定间距素数簇定理。

## 参考文献

[GT10] Ben Green and Terence Tao, *Linear equations in primes*, Annals of Mathematics **171** (2010), 1753–1850. DOI `10.4007/annals.2010.171.1753`.

一般有限复杂度情形使用 Green–Tao 的 Möbius–nilsequence 定理与 Green–Tao–Ziegler 的 Gowers 逆定理所完成的无条件版本。

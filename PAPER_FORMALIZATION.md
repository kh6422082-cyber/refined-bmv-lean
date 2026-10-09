# 论文形式化状态：必要主结论及其依赖已闭合

对应论文 **Dimension-independent lower bounds for matrix-word averages at low degrees**（初始 v0.1，2026-10-09）。公开仓库入口和定理对应表见 [README.md](README.md) 与 [THEOREM_MAP.md](THEOREM_MAP.md)。原始论文内容 SHA256 为 `c5b58c399fcc2bfe2044157d1e81273f62e24544fb2c6ba27abbbf8fded63dee`。

截至 2026-10-10，论文必要主结论及其证明依赖全部闭合。已证明全部六个有限对的 PSD 强下界、33 定量结论、任意正次数的一 B/二 B 边界、完整非对易指数桥、推论 2.3 的整个区域及 54 的指数等号分类。全部实际使用的 ALT 参数族均有独立证明。当前 55 个交付源码文件核验通过，200 条公理依赖审计仅包含通常基础。

这不宣称逐式复刻整篇论文：任意实数参数的全范围 ALT 背景定理未单独形式化，部分原稿中间步骤由完整替代证明取代。机器状态用 `required_main_results_complete=true` 表示必要结论已经完成，并保留 `paper_coverage_complete=false` 作为严格逐式全文覆盖的状态。

## 已完成的论文节点

| 论文位置 | Lean 定理 / 文件 | 范围 |
|---|---|---|
| (1.1)，任意 n,m 的全部词与归一化 | `balancedWords_length`, `balancedWords_nodup`, `complete_average_trace_real` | 完整位置词，基数 choose(n+m,n)，无重复；Hermitian 输入的完整平均为实 |
| 定理 2.1，(2.2) | `paper_theorem_2_1_psd`，`PaperMain.lean` | 任意有限维 A,B PSD：p44 ≥ Tr H⁴ ≥ Tr(AB)⁴ = T44，包括奇异 A |
| 定理 2.2，(2.3) | `paper_theorem_2_2_psd`，`PaperMain.lean` | 任意有限维 A PSD、B 任意 Hermitian：p54 ≥ U54 ≥ T54 ≥ 0 |
| 定理 2.2，P=U 的等号 | `paper_theorem_2_2_equality` | A 正定、B Hermitian：P54=U54 当且仅当 AB=BA |
| 引理 3.1，实际非对易乘积极限 | `symmetric_trotter_tendsto`, `symmetric_trotter_tendsto_multiple`，`SymmetricTrotter.lean` | 任意 complex F,G、d≥1，算子范数下对称乘积的 k 次及 mk 次幂极限；无需 Hermitian 或对易 |
| 引理 3.1，CFC 分数幂对应 | `cfcTrotterStep_eq`, `cfc_trotter_tendsto`，`ExponentialBridge.lean` | 正定 D,B，论文 (3.2) 的实际矩阵乘积收敛到 exp(m(log D+log B)) |
| 引理 3.1，CLBRIDGE | `paper_lemma_3_1` | 每个正整数 n,m、正定 A,B：L(n,m)≤T(n,m)，无对易前提 |
| 指数迹的完整复数解释 | `paperL_matrix_posDef`, `paperL_trace_real`, `paperL_trace_eq_real`, `paperL_nonneg` | log 线性组合的指数为正定，完整复迹等于实数值 paperL；论文应用要求输入正定 |
| 推论 2.3，完整区域 | `paper_corollary_2_3`，`PaperResults.lean` | 正定 A,B、正整数 n,m：min(n,m)≤2 或六个指定有限对时 p≥L |
| 推论 2.3，PSD 有限部分 | `paper_corollary_2_3_finite_psd` | 六个有限对的全部 p≥T 比较，含奇异 PSD 输入 |
| 定理 2.1，指数后果 | `paper_theorem_2_1_exponential` | 正定 A,B：p44≥L44 |
| 定理 2.2，完整指数链与等号 | `paper_theorem_2_2_exponential`, `paper_exponential_equality54` | 正定 A,B：p54≥U54≥T54≥L54，且 p54=L54 当且仅当 AB=BA |
| (2.5)，对易输入 | `paper_commuting_equalities`，`Commuting.lean` | 正定对易 A,B 及正整数 n,m：p=T=L=Tr AⁿBᵐ，包括普通矩阵 log/exp |
| (2.6) | `p_letter_exchange`, `paperL_exchange` | 任意次数的输入/次数交换对称 |
| 命题 3.2，一 B | `paper_proposition_3_2_one`，`OneLetter.lean` | 每个正整数 n：p(n,1)=T(n,1) |
| 命题 3.2，二 B | `paper_proposition_3_2_two`，`TwoLetterBoundary.lean` | 每个正整数 n、任意有限维 A PSD、B Hermitian：完整 p(n,2)≥T(n,2)，包括奇异 A |
| (3.6) 标量步骤 | `two_letter_scalar_average`，`TwoLetterScalar.lean` | 每个 n，非负标量 a,b 的单项式平均 ≥ (ab)^(n/2)，包括零特征值 |
| (4.4) | `identity43`, `p43_ge_W` | 两交换子平方和 p43≥W43 |
| 命题 4.1，(4.1) | `paper_proposition_4_1_psd`，`Strong43.lean` | 完整 PSD 强链 p43≥W43≥T43，包含奇异输入；r=3,q=1 比较由已证明的 cubic 链推出 |
| (3.4)，反向目标 | `reversed45_posDef`, `reversed45_psd`，`Reversed45.lean` | PSD A,B：T45(A,B)≤T54(B,A)，保留两个不同的有向目标，不将其误写成相等 |
| (4,5) 强结论 | `paper_strong_4_5_psd` | PSD A,B：p45≥T45；由目标比较、p 的字母交换与强 54 链实际合成 |
| (3.1)，全部实际使用参数 | `alt_natural_posDef`, `alt_natural_psd`, `alt_rational_sandwich_psd`，`ALTFamilies.lean` | 任意正整数 q、自然数 n≥q 的 r=n/q 夹心 ALT，PSD 输入含奇异矩阵 |
| (3.1)，整数参数族 | `alt_integer_psd`, `alt_integer_sandwich_psd` | 每个正整数 k,q 的 r=k 比较，两个参数均无上限 |
| (3.2)，实际有限步 | `alt_trotter_approximants_le` | 每个正整数 k,m、PSD D,B：Tr(D^(1/(2k)) B^(1/k) D^(1/(2k)))^(mk)≤Tr(sqrt(D) B sqrt(D))^m |
| (3.3)，反向目标 | `reversed34_posDef`, `reversed34_psd`，`Reversed34.lean` | PSD A,B：T34(A,B)≤T43(B,A)，保留两个不同有向目标并包含奇异输入 |
| (3,4) 强结论 | `paper_strong_3_4_psd` | PSD A,B：p34≥T34；由有向目标比较、字母交换和强 43 链实际合成 |
| 引理 6.1，(6.3) | `sandwich_fourth_le` | Hermitian J、PSD C 的完整夹心四次矩比较 |
| (7.3)–(7.4) 的复迹函数 | `cubicStripTrace_entire`, `cubicStripTrace_center_symmetry`, `cubicStripTrace_midpoint_real` | 完整复迹函数全纯、中心对称；正定输入的实参数与 CFC 实幂一致 |
| (7.3) 的条带有界前提 | `complexPower_imaginary_unitary`, `complexPower_norm_realpart`, `cubicStripTrace_bounded_strip` | 虚幂为酉矩阵，范数只依赖实部，任意有限宽闭条带有界 |
| (7.5) | `cubic_center_deficit`, `cubic_center_le_endpoint`，`CubicCenter.lean` | PSD 输入的精确交换子平方恒等式及中心值≤端点值 |
| (7.5) 后的中心值性质 | `cubic_center_pos`, `cubic_center_trace_real` | sqrt 形式的中心迹确为实数；正定输入及 d≥1 时严格为正 |
| (7.6) | `cubicStripTrace_boundary_factorization` | 在 1/4+it 边界按原稿顺序分解完整复迹，无交换不同矩阵的假设 |
| (7.7) | `trace_holder_442`, `cubicStripTrace_left_bound`，`TraceHolder.lean` / `CubicStrip.lean` | 完整复迹的 Hilbert–Schmidt Cauchy–Schwarz、4/4/2 Holder、酉不变性及精确 √(d₀c₀) 边界界 |
| (7.8) | `cubicStripTrace_sharp_strip` | 在完整闭条带 [1/4,3/4] 上应用已证明的三线定理，保留中心相关的精确界 |
| (7.9)–(7.10) | `even_disk_point_lower`，`EvenDisk.lean` | 偶全纯单位圆盘函数的实部下界，包含 a=1 的常数情形 |
| (7.11) | `stripDiskInverse_differentiable`, `stripDiskInverse_maps_strip`, `stripDiskInverse_neg` | Cayley 比值实部>0，主值 log 在整个圆盘上解析；映入所需条带且中心偏移为奇函数 |
| (7.11)–(7.12) 特殊点 | `stripDiskInverse_cubic_point`, `cubicDiskPoint_norm_sq` | 1/√3 的范数平方=1/3，并精确映射到 2/3 |
| (7.11)，实际反函数恒等式 | `stripDiskInverse_tan_right_inverse` | 单位圆盘上 tan(π(z−1/2)) 确实恢复原点 w；主值 log 公式不只是形式定义 |
| (7.12) | `cubicStripTrace_point_ratio_bound`，`CubicAnalytic.lean` | 任意维数正定 X,Y 的完整一点比值估计，参数为 C/√(DC) |
| (7.13)，矩阵联合比较 | `paper_cubic_joint_psd`，`CubicMatrix.lean` | A,B PSD 且 d≥1：D+2W≥3C，C=Tr(A^(3/2)B^(3/2))²；CFC 幂和实际矩阵矩完全对应 |
| (7.13)，定量矩阵余量 | `paper_cubic_quantitative_posDef` | 正定输入下有 a∈[0,1]、C=Da² 且 D+2W−3C≥3D(1−a)²(1+a)/(3−a) |
| (7.14)，独立 ALT 实例 | `cubic_alt_posDef`, `cubic_alt_psd`，`CubicALT.lean` | 任意有限维 PSD A,B：C≥S；极分解、加权酉迹界、4/4/2 Holder 与三线定理给出实际证明 |
| 命题 7.1，(7.1) | `paper_proposition_7_1_psd` | 完整 PSD 强链 D+2W≥3C≥3S，且 p33≥S=T33，包括奇异输入 |
| 命题 7.1，(7.2) | `paper_proposition_7_1_quantitative`，`CubicQuantitative.lean` | PSD 输入且 D>0，实际 x=√(C/D)：D+2W−3S≥3(C−S)+3D(1−x)²(1+x)/(3−x) |
| (7.15)，中间平均估计 | `cubic_average_ge_joint_moment` | 完整平均 p33≥(9C+S)/10；与已证明的 C≥S 合成最终强下界 |
| 交替整数乘积矩的实性与正性 | `product_nat_trace_real`, `product_nat_trace_nonneg` | 任意 k：A PSD、B Hermitian 时 Tr(AB)^k 为实；A,B PSD 时该迹非负，包含三次矩 S |
| (7.10) 的代数圆盘计算 | `mobius_disk_left_bound`，`CubicScalar.lean` | 从明确的圆盘二次约束推出最左实坐标；完整全纯圆盘步骤见上方 EvenDisk 与 CubicAnalytic |
| (7.13) | `cubic_margin_identity`, `cubic_joint_of_ratio_bound` | 精确标量恒等式、余量非负、从已给定比值估计到联合估计的标量步骤 |
| (7.15) | `identity33`, `cubic_average_deficit` | 完整20词分类与平均差值恒等式 |
| 附录 A/B | `certificate44`, `certificate44sos`, `certificate54` 等 | 完整70/126词、原有理 Gram、四平方、正权及矩阵解释 |

所有矩阵强结论量化 `d : ℕ` 和任意输入矩阵，没有维度或谱宽限制。矩阵实幂用 **连续函数演算 CFC** 明确定义，避免把函数类型上的逐元素幂误当作矩阵幂。Lean 中数值比较用 `reTrace`，同时证明完整平均、U54 和乘积四次矩的迹确为实数；这保留了论文的复矩阵输入域。

## 与论文证明组织的变化

44 的谱比较使用开源 Schur 三角化证明，在本机重新编译，并用 `charpoly(AB)=charpoly(sqrt(A) B sqrt(A))` 直接处理奇异 A。Hermitian 四次矩控制对角四次幂的步骤由平方和证明；这里无需把 H 假设为 PSD。第三方来源和兼容性修改见 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)。

54 的 P=U 等号先由四个正权平方为零得到 AB normal，再用已形式化的 Fuglede 定理推出 A² 与 B 对易，最后由正平方根函数演算得到 A 与 B 对易。这替代了原稿中的 normal 矩阵实谱论证；输入假设与结论保持对应。

二 B 命题采用更强的逐词估计：每个词经循环取迹化成 Tr AᵏBAⁿ⁻ᵏB；对称谱权重配合成对 AM–GM，使每个词都≥T(n,2)，再由完整词计数与归一化得到平均下界。此路线直接覆盖零特征值，也只要求 B Hermitian。原稿的均匀间隙平均恒等式 (3.5) 未单独形式化；已完成的命题不依赖它。谱展开公式和目标矩的 CFC 解释均已证明。

33 的复幂定义为 exp(z·log A)，实参数与正定矩阵的 CFC 实幂一致。全纯性、边界 Holder 和三线定理针对完整复迹证明，未将 Re f 当作全纯函数。一般有限条带有界性用来满足三线定理前提，最终输出的是精确 √(d₀c₀) 界。圆盘步骤利用偶性推出中心导数为零，再用二阶 Schwarz 引理；这替代了构造 H(w²) 的组织方式。Cayley 比值和主值 log 的全圆盘域、奇性及实际取值均已核验。最后用 A+εI、B+εI 及 PSD 锥上的 CFC sqrt 连续性完成联合矩估计的奇异输入延拓。

(7.14) 没有导入一个未经证明的 ALT 目标。代码先对 M=A^(1/2)B^(1/2) 构造 M=UP，P 正定、U 酉；再插值 Tr A^(3z/4)B^(3z/4)P^(6−3z/2)U*。左边界由正权与酉矩阵的完整复迹模界控制，右边界由 4/4/2 Holder 控制。中心点和两端矩均精确识别，标量插值推出 S≤C。CFC 连续性把此独立实例延拓到 PSD 输入。定量余量的实际 √(C/D) 参数也通过连续性延拓，覆盖奇异输入且 D>0 的情形。

(3.4) 使用同一路线的八次矩版本。两个 Hilbert–Schmidt 步骤与交换子平方先给出 8/8/4/2 Holder，再插值 Tr X^(5z/8)Y^(5z/8)P^(10−5z/4)U*，独立证明 r=5/4,q=4 实例。CFC log/exp、幂的复合及 PSD 锥上的幂连续性完成实际有向目标的对应和奇异输入延拓。43 所需的 r=3,q=1 比较则由 S≤C≤D 直接得到，再通过 A^(1/3) 与夹心矩的精确恒等式接到 W43≥T43。

本轮的通用 ALT 证明先写 M=UH，对任意正整数 q 插值复迹 G(z)=Tr U H^(qz) P^(N(1−z/2)) V。左边界由正权酉迹界控制，右边界由 Hilbert–Schmidt Cauchy–Schwarz 控制；在 z=1/q 得到完整复迹的 2q 阶加权 Holder 界。外层再对 A^(1/2)B^(1/2)=UP 插值 Tr A^(nz/(2q)) B^(nz/(2q)) P^(2n−nz/q) U*，在 z=q/n 恢复 Tr P^(2n)。这给出全部正整数 q、n≥q 的 r=n/q 比较。两层复迹的全纯性、完整闭条带有界性、虚幂酉性、端点与目标矩对应均在 Lean 中证明；PSD 锥上 CFC 幂的连续性完成奇异输入延拓。整数 r=k 族及 (3.2) 随后由精确幂复合与循环迹恒等式得出。

(3.1) 对任意实数 r≥1、q>0 的全范围背景版本未单独形式化。本轮完成的是论文的全部实际使用参数族；任何已交付应用均未把全范围 ALT 作为公理或隐藏前提。详见 [alt_completion.json](verification/alt_completion.json)。

非对易乘积极限采用一阶证明。一般赋范环中，两个函数在 0 的值均为 I、导数相同，则一步差值为 o(t)，而函数范数局部≤1+C|t|。已证明的非对易幂差估计给出 k 步误差≤exp(C)·k·||f(1/k)−g(1/k)||→0。对称指数乘积与 exp(t(F+G)) 具有相同的导数 F+G，后者的 k 次幂精确等于 exp(F+G)。连续取 m 次幂得到 mk 次极限，再将 CFC 正幂逐项识别为 exp(t log A)。最后把已证明的 (3.2) 有限步不等式传到极限，得到任意正整数 n,m 的 L≤T。

推论 2.3 按原稿的区域定义为 min(n,m)≤2 或六个指定有限对，代码没有扩大为整个 n,m≤5 矩形。54 指数等号先由 p= L 与四项不等式链迫使 p=U，使用已完成的 P=U 对易分类；反方向使用任意正次数的对易 p/T/L 等式。没有使用未经证明的 ALT 等号条件。

## 完成范围与未逐式形式化的部分

必要主结论与全部证明依赖已完成，[paper_coverage.json](verification/paper_coverage.json) 的 `remaining_required_proofs` 为空，`required_main_results_complete=true`。

严格逐式全文覆盖保留 `paper_coverage_complete=false`：

- (3.1) 的任意实数 r≥1、q>0 全范围 ALT 背景版本未单独形式化。全部实际使用参数族均已证明，主结论不依赖这个背景版本。
- 原稿的均匀间隙恒等式 (3.5)、辅助函数 H(w²) 及 Lie–Trotter 证明里的矩阵 log 级数中间步骤未逐式复刻；相应命题均由上面列出的完整替代证明闭合。

所有范围差异均明示，没有用目标公理、占位证明或隐藏假设填补。最终范围摘要见 [exponential_completion.json](verification/exponential_completion.json)。

## 重现与审计

在 `lean_latest` 下运行 `python scripts/verify.py`。脚本按依赖顺序编译全部交付源码，并打印核心新定理及上游 Schur 定理的公理依赖。

当前 55 个交付源码文件全部通过核验，200 条公理依赖审计只包含 propext、Classical.choice、Quot.sound。本轮 `python scripts/verify.py --incremental` 实际重编 6 项，复用 49 项已验证哈希。增量模式仅复用上一成功记录中源码和 olean 哈希均一致、且本次没有重编依赖的条目；汇总公理审计总是重新运行。报告逐项标记实际重编或已验证哈希复用。默认无参数模式仍执行完整重编。

- [最终构建记录](verification/build_report.json)：源码/olean SHA256、退出码和时间。
- [完整编译输出](verification/build.log)。
- [公理依赖输出](verification/axioms.log)。

`all_passed` 表示交付源码全部通过编译；必要主结论与严格全文覆盖分别由上面两个状态字段记录。交付源码不使用 `sorry`、`admit`、自设目标公理或 `native_decide`。

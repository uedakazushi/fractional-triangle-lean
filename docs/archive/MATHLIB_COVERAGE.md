# 固定版 API 実査

2026-09-19。Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b)、
mathlib 5ed2965256430c3649e86755f9576b54eca72435。
`validation/session_20260919/api_spike.stdout.log` は実際の `#check`、exit 0。
以下の宣言は `import Mathlib` のスパイクで確認した。右欄は固定ソース内の定義元。

|目的|確認した宣言|定義元 import|
|---|---|---|
|多項式と偏微分|MvPolynomial, MvPolynomial.pderiv, pderiv_pow|Mathlib.Algebra.MvPolynomial.PDeriv|
|商代数写像|Ideal.Quotient.mkₐ, mkₐ_surjective|Mathlib.RingTheory.Ideal.Quotient.Operations|
|群値斉次成分|MvPolynomial.weightedHomogeneousSubmodule, IsWeightedHomogeneous.mul|Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous|
|成分の積|MvPolynomial.weightedHomogeneousSubmodule_mul|同上|
|成分像・和|Submodule.mem_map, Submodule.iSup_induction, Submodule.mul_mem_mul|各宣言を api_spike で確認|
|次数群|AddSubgroup.closure, QuotientAddGroup.mk', QuotientAddGroup.eq_zero_iff|Mathlib.GroupTheory.QuotientGroup.Basic 等|
|実環同型|AlgEquiv, AlgEquiv.ofBijective, Subalgebra.equivOfEq, Subalgebra.topEquiv|Mathlib 全体で確認|
|局所化|Localization, IsLocalization.injective|Mathlib.RingTheory.Localization.Basic 等|

実装済み: 群の商、実際の複素商環、成分の像、成分の和の乗法閉性、根部分代数、
全複素点を量化する孤立性、および全nの Fermat 偏微分と孤立性。
`CoxDegrees.lattice_degree` は任意の AddCommGroup 内の等式なので torsion を捨てない。

以下の既存完全定理は、確認できたものとして使用していない:
孤立超曲面の正規性、有限群商の局所完備化交換、三変数の極/signature復元、
可逆表示への一般帰着。これらを一括して供給するライブラリ定理があるとは主張しない。

最初のAPI名探索の失敗はログに保存した。未知の名前を本番ソースの仮定に置き換えていない。

## 追加実査

`validation/session_20260919/expanded_api.stdout.log` は追加検査の実ログ（exit 0）。
APISpikeにInt.emod_add_ediv_mul、Finset.lcm_dvd/dvd_lcm、Nat.isCoprime_iff_coprime、
IsCoprime.prod_right、Finset.prod_erase_mul、Finsupp.weight_eq_sum、MvPolynomial.coeff_X_powを追加。
実際の群作用では一般Module用のsum_smulと整数zsmulのAPIを区別し、
必要な有限和の等式は群の公理から帰納的にも証明した。失敗したAPI探索はログに保持。

## 余接空間・局所環の追加実査と使用

以下は今回の7モジュールのビルドで実際に使用した固定版APIである。

|目的|使用した宣言|定義元|
|---|---|---|
|原点イデアルの二乗|MvPolynomial.mem_pow_idealOfVars_iff', Finsupp.range_single_one|RingTheory.MvPolynomial.Ideal, Data.Finsupp.Weight|
|実余接空間|Ideal.Cotangent, Cotangent.lift, mapCotangent, toCotangent_eq_zero|RingTheory.Ideal.Cotangent|
|商写像の核と像|Ideal.mem_map_iff_of_surjective, map_pow, Quotient.liftₐ|RingTheory.Ideal.Maps, Ideal.Quotient.Operations|
|局所化での冪商の保存|IsLocalization.AtPrime.under_maximalIdeal_pow, equivQuotMaximalIdealPow|RingTheory.Localization.AtPrime.Basic|
|実局所余接空間と正則性|IsRegularLocalRing.iff_finrank_cotangentSpace|RingTheory.RegularLocalRing.Defs|
|超曲面の次元上界|ringKrullDim_quotient_succ_le_of_nonZeroDivisor|RingTheory.KrullDimension.NonZeroDivisors|
|多項式環の次元|MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite|RingTheory.KrullDimension.Polynomial|
|局所化の次元|IsLocalization.AtPrime.ringKrullDim_eq_height|RingTheory.Ideal.Height|

完備化交換や安定化群不変環の具体的同型は、これらだけでは供給されない。

## 有限自由表示とHilbert級数の追加実査

以下は固定mathlib版でソースを確認し、新7モジュールの証明に実際に使用した。

|目的|使用した宣言|定義元|
|---|---|---|
|係数環を拡大した基底|Finsupp.linearCombination_smul, curryLinearEquiv, Module.Basis.mapCoeffs|LinearAlgebra.Finsupp, LinearAlgebra.Basis|
|代入写像の像|MvPolynomial.aeval_range, AlgEquiv.ofInjective|Algebra.MvPolynomial, Algebra.Algebra.Equiv|
|有限生成性・Noether性|Algebra.FiniteType.equiv, trans, isNoetherianRing|RingTheory.FiniteType|
|成分基底の濃度|Module.finrank_eq_nat_card_basis, Nat.card_sigma, Sym.equivNatSumOfFintype|LinearAlgebra.Dimension.StrongRankCondition, SetTheory.Cardinal.Finite, Data.Sym.Card|
|共通分母の母関数|PowerSeries.invOneSubPow, invOneSubPow_inv_eq_one_sub_pow|RingTheory.PowerSeries.WellKnown|
|次数のN倍への置換|PowerSeries.expand, coeff_expand, expand_X|RingTheory.PowerSeries.Expand|
|有限次数シフト|PowerSeries.coeff_X_pow_mul'|RingTheory.PowerSeries.Basic|
|有理関数と形式冪級数の共通の体|HahnSeries.ofPowerSeries, RatFunc.coeToLaurentSeries, coe_X|RingTheory.LaurentSeries|

有限自由性からKrull次元の等式を自動で供給する定理は使用しない。
今回、素イデアルの鎖を用いる一般整拡大の次元定理をIntegralDimensionに実装した。
正規性・整域性・次元の等式を追加の未充足classで仮定していない。


## 超曲面の実Hilbert級数と数値的必要条件

|目的|使用した固定版API|定義元|
|---|---|---|
|商成分の有限性|weightedHomogeneousSubmodule_fg, Module.Finite.of_surjective|RingTheory.MvPolynomial.WeightedHomogeneous, LinearAlgebra.FiniteDimensional|
|斉次積の射影|DirectSum.coe_decompose_mul_of_left_mem|Algebra.DirectSum.Decomposition|
|実成分完全列の次元|LinearMap.finrank_range_add_finrank_ker, finrank_range_of_inj|LinearAlgebra.FiniteDimensional.Lemmas|
|重み付き単項式基底|MvPolynomial.basisRestrictSupport, weightedHomogeneousSubmodule_eq_finsupp_supported|RingTheory.MvPolynomial.Basic, RingTheory.MvPolynomial.WeightedHomogeneous|
|母関数の積係数|PowerSeries.coeff_prod, Finset.finsuppAntidiag|RingTheory.PowerSeries.Basic, Algebra.Order.Antidiag.Finsupp|
|多項式と形式冪級数|Polynomial.coeToPowerSeries.ringHom, coe_injective|RingTheory.PowerSeries.Basic|
|分子・分母の次数|Polynomial.natDegree_eq_of_le_of_coeff_ne_zero, natDegree_prod, natDegree_pow|Algebra.Polynomial.Degree, Algebra.Polynomial.BigOperators|
|単純零点因子の消去|mul_neg_geom_sum, Polynomial.evalRingHom|Algebra.Ring.GeomSum, Algebra.Polynomial.Eval|

この数値的必要条件の固定版APIと証明項は、前回追加した8モジュールを参照。API探索の失敗ログも保存している。

## 有限箱の数え上げと整拡大の次元

|目的|使用した固定版API|定義元|
|---|---|---|
|剰余の有限型|ZMod.val_natCast_of_lt, natCast_zmod_val, intCast_eq_intCast_iff_dvd_sub|Data.ZMod.Basic|
|有限全単射の濃度|Nat.card_congr, Nat.card_sigma, Equiv.piCongrRight|SetTheory.Cardinal.Finite, Logic.Equiv|
|素イデアル鎖の収縮|Ideal.IsIntegral.under_lt_under|RingTheory.Ideal.GoingUp|
|lying over|Ideal.nonempty_primesOver|RingTheory.Ideal.GoingUp|
|鎖の持ち上げ|Ideal.exists_ltSeries_of_hasGoingUp|RingTheory.Ideal.HasGoingUp|
|整拡大のgoing up|Algebra.HasGoingUp.of_isIntegral|RingTheory.Ideal.HasGoingUp|
|次元の比較|Order.krullDim_le_of_strictMono|Order.KrullDimension|
|多項式環の正確な次元|MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite|RingTheory.KrullDimension.Polynomial|

RootDimensionのAlgebra.IsIntegralインスタンスはModule.Finiteから合成し、実際のビルドで検証した。

## 実次数商の複素指標

`QuotientAddGroup.mk'_surjective`と`Finite.of_surjective`で実L/ℤτの有限性を証明した。
`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`、
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`は
`Mathlib.GroupTheory.FiniteAbelian.Duality`の固定版ソースを確認して使用した。
ℂ上の`HasEnoughRootsOfUnity`は`RingTheory.RootsOfUnity.AlgebraicallyClosed`の
`IsSepClosed.hasEnoughRootsOfUnity`。有限群のexponentの非零性をℂへ明示的に移して供給する。

## 指標作用と巡回不変環

|目的|実際に使った固定版API|定義元|
|---|---|---|
|内部斉次分解上の作用|DirectSum.toAlgebra, decomposeAlgEquiv, decompose_lhom_ext|Algebra.DirectSum|
|不変拡大の整性と素点軌道|Algebra.IsInvariant.isIntegral, exists_smul_of_under_eq|RingTheory.Invariant|
|整な有限型拡大の有限性|Algebra.IsIntegral.finite|RingTheory.FiniteType|
|局所化した作用と包含|IsLocalization.algEquivOfAlgEquiv, liftAlgHom, algHom_ext|RingTheory.Localization|
|巡回群の位数・分離|Complex.card_rootsOfUnity, isPrimitiveRoot_exp, IsPrimitiveRoot.pow_inj|RingTheory.RootsOfUnity|
|巡回商の単項式基底|AdjoinRoot.powerBasis', Module.Basis.smulTower, injective_constr_of_linearIndependent|RingTheory.AdjoinRoot, LinearAlgebra.Basis|
|不変加群への平均化|Representation.averageMap, averageMap_invariant, averageMap_id|RepresentationTheory.Invariants|
|実際の完備化関手|AdicCompletion.map, map_comp, congr|RingTheory.AdicCompletion.Functoriality|

有限群の平均化も完備化も新しく定義し直していない。両APIの間に必要な分裂・像の
同定をCompletionInvariantsで証明し、元のroot環へ適用した。
局所完備化の因子分解と形式的座標消去を一括して供給する定理は、まだ見つけていない。

環としての完備化にはIdeal.quotientMapₐ、Submodule.Quotient.restrictScalarsEquiv、
Ideal.smul_top_eq_mapを使用し、既存のAdicCompletion型の冪商を同型化した。
LocalCompletionではIsLocalization.AtPrime.equivQuotMaximalIdealPowを全冪で使用する。
RootLocalCompletionの最終合成は型クラス探索が重いため、その一宣言と対応テストだけ
有限のelaboration予算を引き上げた。カーネル検査や公理監査は省略していない。


## 有限閉ファイバーと一点不変環

利用した既存APIはAlgebra.QuasiFinite.finite_primesOver、Ideal.radical_eq_sInf、
Ideal.exists_radical_pow_le_of_fg、Ideal.prod_eq_iInf_of_pairwise_isCoprime、
Ideal.quotientInfRingEquivPiQuotient、Ideal.map_isPrime_of_equiv、
Ideal.map_equiv_liesOver、IsLocalRing.map_ringEquiv_maximalIdeal。
冪商の射影系を接続してAdicCofinality/AdicChineseRemainderを構成し、
原作用の同変性・一点支持の持ち上げ・有限和の平均化を追加した。
依存mathlibのソースは変更していない。

次の形式的座標段階に向けて、MvPowerSeries.toAdicCompletionAlgEquiv、
Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq、
Algebra.FormallyUnramified.comp_injective、StandardEtalePairとPowerSeries.binomialSeriesを
固定版ソースで確認済み。これらが現在のFermat局所環に適用済みとは主張しない。
AdicCompletion.spanFinrank_maximalIdeal_eqは、非正則性を元の局所環に移す際の
既存APIとして確認済みである。

## Hensel形式座標と完備局所余接次元

|用途|使用した既存API|mathlibソース|
|---|---|---|
|完全環での単純根の存在|HenselianRing.is_henselian|RingTheory.Henselian|
|同じ剰余を持つ単純根の一意性|IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub|RingTheory.Henselian|
|完備環とその再完備化|AdicCompletion.ofAlgEquiv|RingTheory.AdicCompletion.Algebra|
|元の環による近似|AdicCompletion.pow_smul_top_eq_ker_eval|RingTheory.AdicCompletion.Completeness|
|写像の分離|IsHausdorff.funext'|RingTheory.AdicCompletion.Basic|
|完備化の余接次元|AdicCompletion.spanFinrank_maximalIdeal_eq|RingTheory.AdicCompletion.LocalRing|
|局所環同型の極大イデアル|IsLocalRing.map_ringEquiv_maximalIdeal|RingTheory.LocalRing.Basic|
|形式的非分岐性の一意性|Algebra.FormallyUnramified.comp_injective|RingTheory.Unramified.Basic|
|形式的滑らかさの持上げ|Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq|RingTheory.Smooth.AdicCompletion|

Hensel/Newton法や完備化そのものを新規に再実装していない。既存APIを使って、
実Fermat商環への持上げ、逆写像、安定化群作用との同変性を接続した。
次は既存MvPowerSeries.toAdicCompletionAlgEquivを使う。完備化のNoether性に関する
追加インスタンスを仮定する必要はなく、元の局所環の余接次元へ直接戻す経路が閉じている。

## 冪級数固定環とJacobian余接境界で使った既存API

`MvPowerSeries.toAdicCompletionAlgEquiv`、`rescaleAlgHom`、`coeff_rescale`、`coeff_mul`を使用。
形式的冪級数環や代入演算は再実装していない。`Ideal.Cotangent.lift`で係数汎関数と
評価した偏微分を実余接空間へ降ろし、`LinearMap.finrank_range_add_finrank_ker`で
非零偏微分による余接次元減少を証明した。局所化と完備化での余接次元保存には
既存の実装とmathlibのspanFinrank保存を再利用する。
一般のsmooth/étale環の正則性を一括で与える定理は今回の固定版探索では見つからなかった。
この制約を未証明仮定で埋めず、Targetの孤立性から必要な余接次元上限を直接証明した。

## 座標置換と互いに素な次数群

`MvPolynomial.renameEquiv`、`coeff_rename_mapDomain`、`Ideal.quotientEquivAlg`を使って実商環を
移送した。根環は証明済みの斉次成分の和として制限し、追加の商環同型を仮定していない。
`Finset.lcm_eq_prod`、`Fintype.prod_dvd_of_coprime`、既存の整数Bezout APIを使い、
次数1の元を構成した。元の次数群の正規形を再利用して単射性を示し、`AddEquiv.ofBijective`
でL≃ℤを得る。最小単項式生成元の次段階ではGradedAlgebra.FiniteTypeの既存APIを調査中。


## 最終標準加群・JSON の既存 API 利用

固定版の `Mathlib.Algebra.Category.ModuleCat.Ext.Basic` を使い、
`CategoryTheory.Abelian.Ext`、`Ext.linearEquiv₀`、`Ext.contravariant_sequence_exact₁`、
`Ext.contravariant_sequence_exact₃`、`Ext.eq_zero_of_projective` から自由分解の Ext を計算した。
独自の導来圏・Ext・長完全列を再実装していない。
`ShortComplex.ModuleCat`、`Ideal.Quotient`、`LinearMap.quotKerEquivOfSurjective`、
`LinearMap.ringLmapEquivSelf` と既存の商加群構造を接続する固有補題だけを追加した。
商環作用・複素線形性・次数付き Hom の具体計算は本研究の表示に必要な橋渡しである。

十進文字列には Lean core `Init.Data.Nat.ToString` の `Nat.ofDigitChars_ten_toDigits`、
`Nat.toList_repr`、`Nat.isDigit_of_mem_toDigits` と `Int.repr_eq_ite` を利用した。
JSON は `Lean.Json` と既存 TreeMap の lookup 定理を使用し、独自 JSON 表現を作らない。
`DecimalCodec` から `ClassificationPayloadCodec` の実ビルド・任意精度テスト・replay が成功した。

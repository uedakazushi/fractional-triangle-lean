# 完全分類器の意味契約

対象は n≥3、a≥1 の孤立超曲面 canonical-root 環であり、全ての孤立超曲面ではない。
n は最小代数生成元数、環の次元は n−1。同値関係は次数付き複素代数同型である。

## 列挙と独立した数学的対象

`Semantics.lean` と `Target.lean` は列挙器を import しない。
p : Fin n → ℕ、各 pᵢ≥2、Σ1/pᵢ<1 と、
L=(ℤⁿ⊕ℤc)/⟨pᵢxᵢ−c⟩ の実際の元 τ、aτ=c−Σxᵢ を量化する。
L の torsion は保持する。T=ℂ[X]/(ΣXᵢ^pᵢ) の実商の斉次成分から
R=⊕_{m≥0}T_{mτ} を実部分代数として定義する。

`RootHypersurfacePresentation` は正重み、非零斉次多項式、定数項・一次項の消滅、
全ての複素点における勾配零点が原点だけであること、実商環と R の次数付き同型を持つ。
同型・孤立性・斉次性は候補への membership や未証明の分類述語ではない。
最小生成元数 n は任意の複素代数全射に対する下限と n 生成全射の存在で証明する。
標準加群は mathlib の実 Ext¹ と次数付き自由分解から構成し、全整数次数で
κ_m≅R_(m+a) となる商環線形同型を `Target.canonical_parameter` で与える。

## Final.lean の公開四定理

|定理|入力・結論|
|---|---|
|`enumerate_sound`|合法 `Input` と実出力の任意の行に対し `EquationRealizes input e`。正で原始的な整列重み、非負指数、実根の実現、孤立性、最小 n 生成、標準 Ext の a-shift、実際の τ と出力根証人の一致を含む。|
|`enumerate_complete`|任意の `Target input.n input.a` に対し、その実 RootRing と次数付き同型な出力位置がただ一つ存在する。|
|`enumerate_pairwise_nonisomorphic`|異なる出力添字が定める実複素商環の間に次数付き代数同型は存在しない。|
|`cli_payload_correct`|純粋な正常 JSON payload を decode した値は `(n,a,enumerate input)` と厳密に一致する。|

四定理に分類同値・Cox lift・正規形存在・固定環同定を仮定として追加していない。
`Target` の presentation は分類する対象の定義であり、分類先への同型を要求していない。
完全性は重みキーだけの一致でなく、実際の環同型を返す。

## 出力と実行境界

`Main.lean` は合法入力から `Input` を作り `classificationPayload` を出力する。
正常終了は 0、入力エラーは 2。n=3,a=6 の空リストも正常な完全分類結果である。
全整数は任意精度の十進文字列。重みの並べ替えは指数行列の列と単項式行列の行に同期する。
JSON 往復定理は全ての `EquationData` 字段を復元する。
weight_key、ソート済み signature、root などの冗長表示字段は encoder から計算される。
decoder はこれらを正規化対象とし、改変された冗長字段そのもののバイト認証は行わない。
出力される root の式は `rootWitnessJson_arithmetic` と `output_root_witness` で実根に接続する。

`checkEquationList_correct` は具体データの全リスト等式を検査する。
一行の削除・複製・指数や次数の改変は拒否する。係数は 1 以外を decoder が拒否する。
`OutputCertificates.lean` は10入力の具体的な全 EquationData リストとの等式と、
その全リストへの純粋 payload の復号等式をカーネルで証明する。
JSON パーサー、文字列印字、コンパイラー、実行時、OS、SHA256 計算は別の実行境界である。
実行バイト列の外部ハッシュを Lean 内の SHA256 証明と取り違えない。

## 証明経路

次数群の正規形 → 根存在一意性 → 実斉次基底・有限自由性 → Hilbert 恒等式。
三変数は実 Hilbert 極・signature復元・支持解析・原始化・全五型の実根環実現へ進み、
重みキーと実次数付き同型の必要十分条件で重複を除く。
高次元は有限指標の実商作用・R=T^G・点の安定化群と完備局所商・余接空間評価から
pairwise coprime を導き、単項式生成と支持数え上げで最大根性と R=T を証明する。
全入力で完全な整数列挙とこれらの意味論を接続し、実出力の変数順序まで移送する。

一般正規性・一般 Laurent 分数格子などの旧設計の補題の一部は、モニック基底や
直接の単射・全射証明で不要になった。未使用補題まで証明済みとは扱わない。

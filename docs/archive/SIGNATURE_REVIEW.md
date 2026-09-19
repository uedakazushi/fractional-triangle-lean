# 最終四定理の署名・意味の自己監査

この報告はエージェントの自己監査であり、人間の mathematical sign-off ではない。
`Final.lean` の四定理は実装済みで Lean ビルドと推移的公理監査を通過した。
元の完成ゲートの最終結果は `validation/final/` と `STATUS.md` を参照する。
過去の部分成果時点のレビューは `docs/history/SIGNATURE_REVIEW_pre_final.md` に保存した。

## 量化と対象

`Input` の証明字段は n≥3 と a≥1 だけである。
`Target` は全 signature、torsion を保持した実商群内の全根、実際の孤立超曲面表示を量化する。
その定義は候補・列挙器を import せず、列挙 membership、分類同値、Cox lift、
可逆正規形、固定環同定を要求しない。
全複素点での勾配条件、実 Ideal 商、実 AlgEquiv、全次数保存が定義の中身である。
ℂ、等号、孤立性を局所 notation や独自公理で置き換えていない。
具体的な10入力の全リストと実現定理により、対象の存在と空のケースを別々に検査する。

`enumerate_sound` の結論 `EquationRealizes` を展開すると、実根環と出力多項式の同型、
孤立性、正の原始重み、非負指数、全生成写像への下限と n 生成写像、標準 Ext の次数差を得る。
`enumerate_complete` は任意の実 Target から出力添字と実次数付き同型を返し、位置の一意性も証明する。
`enumerate_pairwise_nonisomorphic` は異なる添字間の実同型を否定する。キーの相違だけではない。
`cli_payload_correct` は任意の合法入力の純粋 payload の完全な EquationData 往復である。
IO 自体や出力バイト列全体をカーネルが実行したという主張ではない。

## 環論の接続に隠れた前提がないこと

有限指標の作用は商写像の関係保存を証明して実 T へ降ろし、成分ごとの指標分離で R=T^G を示す。
局所商では全群でなく点の安定化群を使う。完備化・形式冪級数・元の局所余接空間へ接続する。
高次元の pairwise coprime と最大根性は任意の実 presentation から導き、対象の前提に置かない。
三変数の Hilbert データ一致をそのまま環同型とせず、全五型の実写像の単射・全射を証明する。
一般補題の整域性やモニック性は各適用箇所で実際に証明する。

標準加群 `PrincipalExt` は mathlib の derived-category Ext¹ である。
自由分解の短完全性と Ext 長完全列から、実 Ext と主イデアル商の線形同型を得る。
商環作用が元の多項式環作用の降下であることも `principalExtQuotient_smul` で証明する。
標準次数成分は S(-h) から S(-Σw) への斉次 Hom と接続写像から定義し、a を使用しない。
その後、全 m∈ℤ に対して κ_m≅R_(m+a) を証明する。結論を定義に埋め込んでいない。

## 検証の範囲

公理許容範囲は `propext`, `Classical.choice`, `Quot.sound` のみ。
最終四定理の `#print axioms` は推移的依存を含む。全指定宣言の同時監査も追加実行する。
独自 axiom、sorry、admit、native_decide、独自 unsafe、カーネル検査回避は使用しない。
固定版依存ソースと research の保存をハッシュおよび git の tracked diff で確認する。
Leanchecker replay は import 済み環境の再検査であり、依存全体の fresh replay と同一視しない。

10個の具体出力証明書は行ごとの検査でなく、順序・重複を含む全 EquationData の等式である。
SHA256 は実行ログとソースとの外部的な結び付け。暗号学的ハッシュを Lean 内で証明してはいない。
JSON decoder が無視する冗長表示字段と、実際に証明される字段は `SPEC_CONTRACT.md` に明記した。
渡辺の六差分は保存された転記との回帰比較で、掲載誌版・後の訂正の調査ではない。
非最大根が孤立超曲面表示を持たないことは Lean テスト、孤立性の反例データは自由循環作用の整数回帰で検査する。
その反例について全局所商の正則性を別途 Lean 定理にしたとは主張しない。

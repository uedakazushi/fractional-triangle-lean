# STATUS — 完全分類の実装と完成ゲート通過

2026-09-19。状態: **FULL_CLASSIFICATION_VERIFIED**。

`Final.lean` の四定理（健全性・一意完全性・相互非同型・純粋 JSON 往復）が実装され、
元の `scripts/acceptance.sh` を変更せず、依存を含む `lake clean` 後の再構築で通過した。
今回の完成ゲートの所要時間は 4243.0 秒。ログは `validation/final/` と
`validation/session_20260919/final_acceptance.json` に保存する。

- 公理監査: 最終四定理を含む1,601宣言。許容基盤公理3種だけで合格。
- 実行回帰: 35入力、528方程式。三変数 a=1,…,6 の件数14,6,8,8,21,0、a=2,…,30 の総数506。
- 具体証明書: 10入力の全 EquationData リストと純粋 payload 復号の等式をカーネルで証明。
- 改変検査: 行削除・複製・指数と変数順序の不一致・次数変更・係数変更を拒否。
- checker replay: 最終契約・四定理・全リスト証明書を含む5モジュールで成功。
- 保存: research の16ファイルと固定依存9パッケージのソース・revision を照合。

最優先だった有限指標の実商環作用と R=T^G、その後の高次元の局所不変環からの逆方向も
最終分類の実依存に含む。標準加群は mathlib の実 Ext により全整数次数で解釈する。
CLI は正常時終了0、入力エラー2。合法な空の結果も正常出力である。

意味契約は `SPEC_CONTRACT.md`、署名の自己監査は `SIGNATURE_REVIEW.md`、
実依存・原稿対応は `SOURCE_MAP.md` と `docs/PROOF_OBLIGATIONS.tsv` を参照。
人間の mathematical sign-off、OS バイト列の Lean 内認証、全依存の fresh checker replay は
今回の実施内容と区別する。過去の失敗・途中経過は削除せず履歴として保持する。

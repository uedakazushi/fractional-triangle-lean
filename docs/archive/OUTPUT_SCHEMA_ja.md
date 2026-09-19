# 出力フォーマット

参照実装は `canonical-root-equations-reference-v1` を出力する。最終 Lean 版では schema 名と verification status を実態に合わせて変えてよいが、以下の exact data 構造を初版の基準にする。

```json
{
  "schema": "canonical-root-equations-reference-v1",
  "integer_encoding": "decimal strings",
  "status": "ok",
  "verification_status": "REFERENCE_ONLY_NOT_LEAN_VERIFIED",
  "input": {"n": "4", "a": "1"},
  "count": "1",
  "equations": [
    {
      "n": "4", "a": "1",
      "weights": ["42", "258", "602", "903"],
      "relation_degree": "1806",
      "polynomial": [
        {"coefficient": "1", "exponents": ["0","0","0","2"]},
        {"coefficient": "1", "exponents": ["0","0","3","0"]},
        {"coefficient": "1", "exponents": ["0","7","0","0"]},
        {"coefficient": "1", "exponents": ["43","0","0","0"]}
      ],
      "signature": ["2","3","7","43"]
    }
  ]
}
```

これは実際の sample から抜粋した主要フィールド。完全な出力には根の繰り上がり正規形と witness、weight_key、equation_text が付く。上の式は `x4^2+x3^3+x2^7+x1^43=0` であり、重みの順と同期している。省略された witness を上記だけから補って完成証明書とみなさない。

係数・指数・重み・次数・signature を decimal string とし、浮動小数変換をしない。出力順は基準版の決定的な順序とする。完全性が集合について証明された後に、表示順の変更を数学的同値として許可することはできるが、出力証明書の byte hash が変わることに注意する。

最終 Lean 版では `verification_status` を自由な自己申告だけにせず、別ファイルで固定された theorem 名、toolchain、ソースハッシュ、認証した入力とリスト、証明書のハッシュを結ぶ。

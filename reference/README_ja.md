# 非形式検証の参照 CLI

Python 3.10 以降、標準ライブラリのみ。論文の旧コードは `research/current/` から読み、変更しない。

```sh
python3 reference/reference_cli.py 3 5 --format text
python3 reference/reference_cli.py 4 1 --output result.json
python3 reference/test_reference.py --max-a 30
```

これは **Lean formally verified program ではない**。新しい部分は、元の列挙結果を実際の係数・指数・式へ変換し、重みのソートと変数の置換を同期させる処理、根の正規形、および高次元の整数のみの再帰である。比較対象の既存実装は Fraction を用いていた。

JSON 内の数学的整数は十進文字列。JavaScript 等で大整数が浮動小数に丸められることを防ぐためであり、Lean 側も exact decoder を作る。`polynomial` の各要素は係数と指数列を持つ。`equation_text` は補助表示。`witness.generator_permutation_new_to_old` は0始まりの添字である。

正常に対象がない `(3,6)` は `status=ok`、空の equations。`n<3` または `a<1` は非零終了し `invalid_input`。資源中断は成功した空リストにしない。どの出力にも `REFERENCE_ONLY_NOT_LEAN_VERIFIED` を付す。

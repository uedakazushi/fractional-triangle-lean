# 標準元の根から生じる孤立超曲面特異点

2026年9月19日、統合日本語稿 v02。


## v02 の追記：渡辺の arXiv 第1版との比較

- Introduction 第1.3節（PDF 5–6頁）に、渡辺敬一の arXiv:1401.0789v1（2014年1月4日）Section 3 との比較を追加。
- 対象は本稿の三点型根環、1 <= delta <= 6、整列した原始重みキーに限定。
- 原資料の個別項目の件数は 14,6,7,7,17,0、本稿の件数は 14,6,8,8,21,0。
  原資料末尾の集計表をそのまま引用した数値ではない。
- 第9.4節（PDF 23頁）に、差分六例の具体的な可逆関係式と signature を追加。
- 掲載誌版との逐項照合、後日の訂正、三点型以外の範囲については主張しない。
  一般有限性定理の否定、またはこれらの特異点そのものの新発見とも主張しない。
- 主定理と既存の証明は変更していない。研究の全面的な再監査や Lean 検証をした版ではない。

追加ファイル：

- `watanabe_v1_three_point_keys.csv`：公開 PDF の個別項目から転記した51件。項目番号と1始まりの PDF ページを付す。
- `verify_watanabe_comparison.py`：上記転記データと現行列挙との集合差、六つの具体式の重み・行列式・signature・標準形への置換を検査。
- `watanabe_comparison_results.json`：今回の検査結果。
- `CHANGELOG_ja.md`：この改訂の範囲。

原資料： https://arxiv.org/pdf/1401.0789v1

CSV は PDF の人手による転記であり、自動抽出を完了したデータとはしていない。
コードの成功は、転記の完全性や原資料に掲載がないという文献上の判断そのものを認証しない。
原資料の PDF はこの配布物には含めない。
(3-C-19) の `(4,10.17;34)` は `(4,10,17;34)` と読むことを CSV に記録した。

再検査：

```sh
python verify_watanabe_comparison.py
python -O verify_watanabe_comparison.py
```

## 対象

Geigle–Lenzing 次数群 L で次数付けられた
T = C[X_1,...,X_n]/(sum X_i^{p_i}) と、標準元 omega の正整数根 delta*tau = omega に沿う部分環 R のうち、孤立超曲面特異点を定めるものだけを扱う。

主定理は全 n >= 3 での可逆多項式による表示である。n=3 では原始次数 h と指数行列の行列式が等しい表示を選べる。n>=4 では R=T が強制され、pairwise coprime な整数列の defect 方程式に帰着する。非孤立完全交差、gcd forest、平均漸近は含めない。

## 重要な訂正

「与えられた可逆式 f の |det E_f| が h に等しい」ことは、根環から来るための必要条件ではない。同型な適切な可逆表示 g の存在条件である。

例えば f=x^2+y^3+z^8 は原始重み (12,8,3;24)、delta=1、det E_f=48 だが signature (3,3,4) の根環である。同型な g=x^2+xz^4+y^3 には det E_g=24 が成り立つ。

与えられた三変数可逆多項式の必要十分条件は、本文の整数 signature A(W) が三元からなり、delta>0 と数値等式 delta*h/(w_1*w_2*w_3)=1-sum 1/r_i を満たすことで記述する。

## 証明の構成

- 共通部分：次数群の繰り上がり、根の算術、有限自由基底、補元対合による Hilbert 相反式。
- 三変数：有理 Hilbert 級数の一次の極から signature を復元し、七つの支持、二つの分岐型の排除、四つの原始化を経て、元の環への単項式準同型を構成する。
- 高次元：二座標の局所商から pairwise coprimality を先に導き、最小生成元の支持数え上げから R=T を得る。
- 一般可換環論の入力と Lean 化の依存関係は別節・付録に明記した。

旧稿で使われたスタックの復元、変形剛性、随伴公式による種数計算は、本稿の三変数の証明では用いない。ただし正規性判定、局所環、有限商の完備化などの一般可換環論は残る。

## 継承ファイルと原稿

- canonical_root_isolated_ja_v02.tex : LuaLaTeX 本文
- canonical_root_isolated_ja_v02.pdf : 組版済み PDF
- verify_classification.py : 整数による signature、単項式次数、原始化、有限列挙の参照実装
- verify_polynomial_identities.py : Z[a,b,c] の 135 個の恒等式の係数別検査
- verification_results.json : 520 個の三変数同型類（delta=1,...,30）、検査集計、高次元例
- validation_log.txt : 今回の実行環境と実行結果
- SHA256SUMS : このファイル以外の同梱ファイルのハッシュ

## 再生成

LuaLaTeX と ltjsarticle が利用できる TeX Live 環境で：

```sh
lualatex -interaction=nonstopmode -halt-on-error canonical_root_isolated_ja_v02.tex
lualatex -interaction=nonstopmode -halt-on-error canonical_root_isolated_ja_v02.tex
lualatex -interaction=nonstopmode -halt-on-error canonical_root_isolated_ja_v02.tex
```

Python 3.10 以降（標準ライブラリのみ）で：

```sh
python verify_classification.py --output verification_results.json
python -O verify_classification.py --output verification_results.json
python verify_polynomial_identities.py
python -O verify_polynomial_identities.py
```

検査を小さくして試す場合：

```sh
python verify_classification.py --scan 8 --census-max 6 --output small_test.json
```

指数上限 18 の五つの座標形では正指数の重み系 24,396 件を照合した。三変数の同型類数は delta=1,...,6 で 14,6,8,8,21,0。2<=delta<=30 の総数は 506。各 delta の有限ループと共通指数箱の出力も比較する。

もう一つの検査は、パラメータ代入でなく、多項式の全係数が一致することを確認する。いずれも外部 CAS、浮動小数、assert 文に依存しない。

## 証明・形式化の状態

これは証明を記述した研究稿と参照実装であり、著者による最終確認済み・投稿承認済みを意味しない。

Lean ソース、Lean コンパイル成功ログ、Lean の最終定理は含まれない。Python の成功は Lean カーネルによる検証ではない。有限検査を全指数に対する定理の証明に代用しない。

今後の形式化では、一般可換環論を含む依存補題に証明項を与え、最終定理の #print axioms で sorryAx と研究固有の追加公理がないことを監査する。本文のモジュール表は予定区分であり、存在を確認していない mathlib 定理名を列挙するものではない。

## 元の原稿

fractional_triangles_v04.pdf、higher_canonical_roots_v03.pdf、および fractional_triangles_elementary_ja_v05.tex に基づく。元のファイルそのものはこの配布物には含めない。

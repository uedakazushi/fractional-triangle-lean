# 未ビルドの環境検査用の種

`lake build` がこの状態で成功しても、確認されるのは mathlib を使った環境検査の恒等式だけである。分類器、Main.lean、最終分類定理、Audit.lean、Tests.lean はまだない。`scripts/acceptance.sh` はその不足を検出して失敗する。

API を固定した環境で確認してから実装するための開始点であり、最終形式化を装うためのサンプルではない。

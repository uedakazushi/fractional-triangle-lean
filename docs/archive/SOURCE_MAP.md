# 原稿と最終実装の対応

原稿は research/current/canonical_root_isolated_ja_v02.tex。元の研究ファイル16件は保持する。
原稿中の証明候補を公理として import せず、以下の実証明へ接続した。

|原稿の主題・ラベル|Lean の主要モジュール|証明の範囲|
|---|---|---|
|def:rootring / lem:nf / prop:root|Semantics, DegreeNormalForm, RootArithmetic|実商群の torsion を保つ正規形と根判定・一意性|
|lem:pieces / prop:free|AmbientGrading, RootFiniteFree, RootHilbertRational|実成分の基底、有限自由性、Hilbert 恒等式|
|cor:numerical|HypersurfaceNumerics, RootMultiplicityFormula, CanonicalParameter|原始性・次数差・積の公式・実標準 Ext のシフト|
|lem:group|AmbientCharacterAction, RootInvariants|有限指標の実商作用と R=T^G|
|lem:rootpole / lem:coordinatepole / lem:recovermultiset|RootHilbertPoleNumerator, RootPoleProfile, TernaryCoordinateSignature|実 Hilbert 極と signature の復元|
|lem:seven / prop:branched / prop:mutation|TargetFiveWeights, TargetPrimitiveWeights|任意の実対象から五型の原始候補へ帰着|
|lem:coxidentities / prop:principalrealization|CoxIdentities, CoxDegrees, TernaryRealization|整数恒等式と全五型の実根環同型|
|thm:main n=3 / cor:weightkey|TernaryClassification, CandidateKeySemantics|全三変数対象の実同型分類、キー iff 実同型|
|app:local / prop:pairwise|RootFermatFormalInvariants, RootNonregularStratum, HigherCoprimality|実完備局所不変環と余接下限から全対の互いに素性|
|lem:highergenerators / thm:main n≥4|HigherPurePowerGeneration, HigherConverse, HigherClassification|最大根性と高次元の必要十分条件・一意分類|
|prop:algorithm3 / eq:recursivebound|Candidates, ExponentBound, HigherArithmetic|全入力の停止する有限整数列挙と完全性|
|thm:main / thm:finite / sec:lean|OutputClassification, ClassificationContract, Final|全出力の実現、任意対象の一意出現、相互非同型、純粋 JSON 正しさ|
|sec:lean / app:audit|OutputCertificateChecker, OutputCertificates, Audit, Tests|具体全リスト証明書・改変拒否・推移的公理監査|

細かい依存と未使用の一般補題は docs/PROOF_OBLIGATIONS.tsv を参照。
原稿の一般 Laurent 格子、一般正規性、一般 homogeneous division は直接の証明に置換した。
その変更理由と標準加群の補完は THEORY_REPAIRS.md に記録する。

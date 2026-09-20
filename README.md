# Isolated hypersurface fractional triangle singularities

**Authors:** Kenji Hashimoto (橋本健治), Hwayoung Lee, Kazushi Ueda (植田一石).

A Lean implementation of the classification
of isolated hypersurface canonical-root algebras over ℂ, up to graded ℂ-algebra
isomorphism, for minimum generator count `n ≥ 3` and positive parameter `a ≥ 1`.
The blueprint is available [here](https://uedakazushi.github.io/fractional-triangle-lean/blueprint/index.html).

## Build and run

Install [elan](https://github.com/leanprover/elan), Python 3.13, Git and a C toolchain.
The exact Lean version is in `formal/lean-toolchain`; all Lean dependencies are
pinned in `formal/lake-manifest.json`. Keep the manifest when cloning.

```bash
cd formal
lake exe cache get
lake build
lake build canonical_roots
lake exe canonical_roots 3 1
lake exe canonical_roots 3 6
lake exe canonical_roots 4 1
```

A successful empty classification, such as `(3, 6)`, exits with status 0.
Invalid inputs exit with status 2. Integral JSON values use exact decimal strings.
Mathematical termination does not imply practical completion within fixed memory
or time for arbitrarily large inputs. See [the output format](docs/OUTPUT_FORMAT.md).

## Verify

From the repository root:

```bash
bash scripts/verify.sh
# Optional, expensive: the original full-clean acceptance gate.
bash scripts/acceptance.sh
python3 scripts/verify_all_axioms.py validation/final/axioms.log
```

The first command builds the library/executable, checks final signatures and tests,
audits 1,633 declarations, runs the CLI regressions and verifies Blueprint references.
The full-clean gate cleans dependencies too. Do not run it against a shared
symlinked `.lake/packages` cache. Use a standalone checkout with its own dependencies.
[Manual verification](docs/VERIFICATION.md) explains the difference between axiom
checking, theorem meanings and execution boundaries.

## Lean Blueprint

Install Graphviz and a LuaLaTeX/latexmk TeX distribution. On Ubuntu:
`graphviz libgraphviz-dev texlive-luatex texlive-latex-extra latexmk`.

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r blueprint/requirements.txt
python scripts/check_blueprint.py --lean
python scripts/build_blueprint.py --pdf
python scripts/check_site.py
python -m http.server 8000 --directory _site
```

Open `http://localhost:8000/`. The site includes the Blueprint, dependency graph,
PDF and exact source links. A green node is not a substitute for reading its Lean
type or for human review. See [Blueprint details](blueprint/README.md).


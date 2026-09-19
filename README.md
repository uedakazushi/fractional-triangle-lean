# Canonical-root hypersurfaces in Lean

**Canonical English source edition.** A Lean implementation of the classification
of isolated hypersurface canonical-root algebras over ℂ, up to graded ℂ-algebra
isomorphism, for minimum generator count `n ≥ 3` and positive parameter `a ≥ 1`.
The domain is a specific family of root algebras, not all isolated hypersurfaces.

**Authors:** Kenji Hashimoto (橋本健治), Hwayoung Lee, Kazushi Ueda (植田一石).

The final four theorem declarations are in
[`formal/CanonicalRoots/Final.lean`](formal/CanonicalRoots/Final.lean).
The [semantic contract](SPEC_CONTRACT.md) explains their quantifiers and boundaries.
The historical clean build and axiom audit are preserved as evidence; an independent
human mathematical sign-off has not been recorded. New publication checks are
reported separately in [PUBLICATION_VALIDATION.md](PUBLICATION_VALIDATION.md).

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
audits 1,601 declarations, runs the CLI regressions and verifies Blueprint references.
The full-clean gate cleans dependencies too. Do not run it against a shared
symlinked `.lake/packages` cache. Use a standalone checkout with its own dependencies.
[Manual verification](docs/VERIFICATION.md) explains the difference between axiom
checking, theorem meanings and execution boundaries.

## Lean Blueprint

Install Graphviz and a LuaLaTeX/latexmk TeX distribution (Japanese TeX support is
needed for the companion). On Ubuntu: `graphviz libgraphviz-dev texlive-luatex
texlive-latex-extra latexmk`; add `texlive-lang-japanese` for Japanese PDF builds.

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

## Japanese companion and publication

The separate `fractional-triangle-lean-ja` repository contains Japanese exposition of
an exact canonical commit. It does not duplicate the proof library. Its
`upstream.lock.json` records that commit. Repository URLs are kept in
`publication.json`; [publication setup](docs/PUBLISHING.md) explains configuration.
No remote repository or public deployment is created by a local build.

`research/` and original formal sources are preserved byte for byte; old Japanese
self-audits are under `docs/archive/`, with their historical status made explicit.
Code is [Apache-2.0](LICENSE); exposition is [CC BY 4.0](LICENSES/CC-BY-4.0.txt).
Use [CITATION.cff](CITATION.cff) and include the exact canonical commit when citing.

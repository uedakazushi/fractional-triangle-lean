# Lean sources

See the [canonical README](../README.md), [semantic contract](../SPEC_CONTRACT.md)
and [manual verification guide](../docs/VERIFICATION.md).
The adjacent `README_ja.md` is a byte-preserved historical scaffold document;
its initial-status statements describe the original handoff, not this source snapshot.

```bash
lake build
lake build canonical_roots
lake exe canonical_roots 3 1
```

The four public theorems are in `CanonicalRoots/Final.lean`.
`lean-toolchain` and `lake-manifest.json` fix the verification environment.

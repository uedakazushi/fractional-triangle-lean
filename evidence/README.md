# Evidence provenance

`source-manifest.json` hashes the byte-identical formal, research and reference
snapshot copied from the original workspace. `original/` contains the existing
acceptance and audit records from 2026-09-19. Machine-specific absolute paths in
those text logs were normalized to `<original-workspace>` and `<original-home>`;
the logs are not themselves claimed byte-identical to the old files.

Historical logs are not represented as new runs. See `PUBLICATION_VALIDATION.md`
for publication checks and their precise scope. Newly captured detailed logs go
under ignored `validation/`; summarized results are committed for review.

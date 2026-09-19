# Publication preparation

This is a local publication candidate; no GitHub remote has been created or pushed.
The authors approved Apache-2.0 for code and CC BY 4.0 for exposition.

1. Choose a GitHub user or organization. Configure the repository URL with
   `python3 scripts/configure_publication.py --owner OWNER`.
2. Create the remote repository and push only after reviewing the file list.
   Git ignores caches, generated sites, binaries and fresh machine-specific logs.
3. GitHub CI builds and uploads the site as an artifact. For public Pages deployment,
   enable Pages with GitHub Actions as the source, then manually run the Pages
   workflow. That deployment workflow uses the same build and checks. CI execution
   on GitHub is not claimed until the repositories are actually uploaded.
4. After release, add a version/tag and repository URL to CITATION.cff as appropriate.
   Prefer release assets for binaries; do not commit the local macOS executable.

The local proof check reused the installed pinned dependency cache. A full clean
acceptance run is intentionally a separate, manual CI option because it rebuilds
all dependencies. Do not run it against a cache shared with another working tree.

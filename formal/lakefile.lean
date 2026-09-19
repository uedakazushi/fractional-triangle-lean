import Lake
open Lake DSL

package canonicalRoots where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib CanonicalRoots where

lean_exe canonical_roots where
  root := `Main

@[default_target]
lean_lib Certificates where

@[default_target]
lean_lib OutputCertificates where

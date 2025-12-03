import Lake

open System Lake DSL

package CvxLean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

meta if get_config? env = some "scilean" then
require scilean from git
  "https://github.com/verified-optimization/SciLean" @ "master"

meta if get_config? doc = some "on" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.26.0-rc2"

@[default_target]
lean_lib CvxLean

@[default_target]
lean_lib CvxLeanTest

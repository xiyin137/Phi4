import Lake
open Lake DSL

package «Phi4» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require «GaussianField» from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "0ecfc79700ad2bad985ec8a6159849da90534b1e"

require «OSReconstruction» from git
  "https://github.com/xiyin137/OSreconstruction.git" @ "cbab0ad49724b09f547597fe7e04a4f36af2050c"

@[default_target]
lean_lib «Phi4» where

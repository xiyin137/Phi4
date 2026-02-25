import Lake
open Lake DSL

package «Phi4» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require «GaussianField» from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "main"

require «OSReconstruction» from git
  "https://github.com/xiyin137/OSreconstruction.git" @ "main"

@[default_target]
lean_lib «Phi4» where

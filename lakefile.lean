import Lake
open Lake DSL

package «spectral_sequence» {
}

@[default_target]
lean_lib «SpectralSequence» {
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

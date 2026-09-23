import Extraction.LookupWiring

/-! Shared normalization for generated extraction expressions. -/

namespace ZiskFv.AirsClean

open Extraction.LookupWiring

/-- Interpret the neutral term emitted by PIL macros through a closed
translator. Unsupported leaves still fail in the translator's Option
codomain. -/
@[reducible]
def translateTrailingAddZero (f : Expr → Option α) : Expr → Option α
  | .add lhs (.constant "0") => f lhs
  | expr => f expr

end ZiskFv.AirsClean

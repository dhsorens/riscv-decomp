/-
  Refine

  The L3 refinement layer's abstract half: nondeterminism with failure, data
  refinement, and a worked specification. Imports nothing from `Rv64` or
  `Decomp`, so a second project can take it without the machine.

  The bridge to an L2 certificate is `Decomp/Refine.lean`, on the other side of
  the boundary.
-/

module

public import Refine.Nres
public import Refine.Examples.Search

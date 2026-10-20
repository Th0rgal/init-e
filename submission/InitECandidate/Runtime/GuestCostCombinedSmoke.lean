import InitECandidate.Runtime.SourceCostCrepControl
import InitECandidate.Runtime.GuestCostArithmeticFamily
import InitECandidate.Runtime.GuestCostFundingMeasure

/-!
Combined-import smoke module.

The compiler-side cost module `SourceCostCrepControl` defines
`FineCost.score_copy` and `FineCost.score_memory` for trace scoring, and the
guest-side modules used to define the same full names for event-unit scoring,
which only collided once both were imported together. The guest utility layer
now keeps its lemmas under `guest_score_copy` and `guest_score_memory`, so the
two worlds load in one environment. This file exists to make that statement a
compile-time check.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace InitECandidate.Runtime.FineCost

/-- The compiler weights and the guest helper price live in one environment. -/
example : sourceCrepWeights.score (executionWork [.copy 3]) = 24 :=
  score_copy 3

/-- The pinned installed helper AST is exported from the guest module. -/
example : sourceFunctionBody Guest.guestFn_add_sat = addSatDeclaredBody :=
  source_addSat_body

/-- The funding measure used by the invariant-aware loop contract is exported too. -/
example (state : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    guestFrameUsed state frame = funding.used.toNat :=
  guestFrameUsed_eq_funding memory

end InitECandidate.Runtime.FineCost

#print axioms InitECandidate.Runtime.FineCost.guest_score_copy
#print axioms InitECandidate.Runtime.FineCost.guest_score_memory

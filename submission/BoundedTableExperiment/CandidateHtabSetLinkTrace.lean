import CandidateHtabSetLeafShape

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual successful run of the side-store block is either the
`side != 0` arm (`store nip cur; store (nip+8) new_leaf`) or the other arm. -/
theorem candidateHtabSetSideStores_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetSideStores none post events) :
    ∃ (value : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual (.var .local (ofString "side")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word value))) guardEvents ∧
      ((value ≠ 0 ∧
        StatementRun fn s
          (.seq (.store (.var .local (ofString "nip")) (.var .local (ofString "cur")))
            (.store (.op .add [.var .local (ofString "nip"), .const (BitVec.ofNat 64 8)])
              (.var .local (ofString "new_leaf"))))
          none post branchEvents) ∨
       (value = 0 ∧
        StatementRun fn s
          (.seq (.store (.var .local (ofString "nip")) (.var .local (ofString "new_leaf")))
            (.store (.op .add [.var .local (ofString "nip"), .const (BitVec.ofNat 64 8)])
              (.var .local (ofString "cur"))))
          none post branchEvents)) := by
  rw [candidateHtabSetLeaf_sideStores] at run
  cases run with
  | iteYes guard nonzero body =>
      exact ⟨_, _, _, rfl, guard, Or.inl ⟨nonzero, body⟩⟩
  | iteNo guard body =>
      exact ⟨_, _, _, rfl, guard, Or.inr ⟨rfl, body⟩⟩

/-- Splitting either side-store arm into the two actual word stores. -/
theorem candidateHtabSetSideStorePair_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {left right : ExpHOL 64}
    (run : StatementRun fn s (.seq (.store (.var .local (ofString "nip")) left)
      (.store (.op .add [.var .local (ofString "nip"), .const (BitVec.ofNat 64 8)])
        right)) none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F)
      (firstEvents secondEvents : List WorkEvent),
      events = firstEvents ++ secondEvents ∧
      StatementRun fn s (.store (.var .local (ofString "nip")) left)
        none mid firstEvents ∧
      StatementRun fn mid
        (.store (.op .add [.var .local (ofString "nip"), .const (BitVec.ofNat 64 8)]) right)
        none post secondEvents := by
  cases run with
  | seqNext one two => exact ⟨_, _, _, rfl, one, two⟩
  | seqStop terminal _ => exact absurd rfl terminal

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateHtabSetSideStores_trace
#print axioms BoundedTableExperiment.candidateHtabSetSideStorePair_trace

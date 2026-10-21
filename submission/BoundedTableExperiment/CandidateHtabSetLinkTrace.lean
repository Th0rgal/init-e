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

/-- Outer split of the root-or-parent link block: either the root store or the
`pp` scope run. -/
theorem candidateHtabSetLink_outer {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetLink none post events) :
    ∃ (value : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .equal (.var .local (ofString "parent")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word value))) guardEvents ∧
      ((value ≠ 0 ∧
        StatementRun fn s (.store (off "t" 72) (.var .local (ofString "new_int")))
          none post branchEvents) ∨
       (value = 0 ∧
        StatementRun fn s
          (.dec (ofString "pp") .one (.var .local (ofString "parent"))
            (.ite (.cmp .notEqual (.var .local (ofString "dir")) (.const (BitVec.ofNat 64 0)))
              (.store (.op .add [.var .local (ofString "pp"), .const (BitVec.ofNat 64 8)])
                (.var .local (ofString "new_int")))
              (.store (.var .local (ofString "pp")) (.var .local (ofString "new_int")))))
          none post branchEvents)) := by
  rw [candidateHtabSetLeaf_link] at run
  cases run with
  | iteYes guard nonzero body =>
      exact ⟨_, _, _, rfl, guard, Or.inl ⟨nonzero, body⟩⟩
  | iteNo guard body =>
      exact ⟨_, _, _, rfl, guard, Or.inr ⟨rfl, body⟩⟩

/-- Outer split of the actual growth branch: either the grow/reload/re-search
arm or the `skip` arm. -/
theorem candidateHtabSetGrowth_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetGrowth none post events) :
    ∃ (value : BitVec 64) (guardEvents branchEvents : List WorkEvent),
      events = .statement :: .cost (statementUnit + branchMoves fn) ::
        (guardEvents ++ branchEvents) ∧
      CostedExpressionRun s
        (.cmp .lower (loc "cap")
          (.panop .mul [.op .add [lw (off "t" 24),.const 1],.const 2]))
        (some (.val (.word value))) guardEvents ∧
      ((value ≠ 0 ∧
        StatementRun fn s candidateHtabSetGrowSeq none post branchEvents) ∨
       (value = 0 ∧
        branchEvents = [.statement] ∧ post = s)) := by
  rw [candidateHtabSetLeaf_growth] at run
  cases run with
  | iteYes guard nonzero body =>
      exact ⟨_, _, _, rfl, guard, Or.inl ⟨nonzero, body⟩⟩
  | iteNo guard body =>
      cases body with
      | skip => exact ⟨_, _, _, rfl, guard, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- Actual successful growth sequence: `htab_grow`, reload `cap`, then the
re-search call. -/
theorem candidateHtabSetGrowSeq_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetGrowSeq none post events) :
    ∃ (afterGrow afterAssign : PanSemStateFiniteExact 64 F)
      (growEvents assignEvents searchEvents : List WorkEvent),
      events = growEvents ++ (assignEvents ++ searchEvents) ∧
      StatementRun fn s
        (.call (some (none, none)) (ofString "htab_grow") [loc "t"])
        none afterGrow growEvents ∧
      StatementRun fn afterGrow
        (.assign .local (ofString "cap") (lw (off "t" 16)))
        none afterAssign assignEvents ∧
      StatementRun fn afterAssign
        (.call (some (some (.local, ofString "leaf"), none))
          (ofString "htab_find_leaf_path") [loc "t",loc "key"])
        none post searchEvents := by
  change StatementRun fn s
    (.seq (.call (some (none, none)) (ofString "htab_grow") [loc "t"])
      (.seq (.assign .local (ofString "cap") (lw (off "t" 16)))
        (.call (some (some (.local, ofString "leaf"), none))
          (ofString "htab_find_leaf_path") [loc "t",loc "key"])))
    none post events at run
  cases run with
  | seqNext growRun rest =>
      cases rest with
      | seqNext assignRun searchRun =>
          exact ⟨_, _, _, _, _, rfl, growRun, assignRun, searchRun⟩
      | seqStop terminal _ => exact absurd rfl terminal
  | seqStop terminal _ => exact absurd rfl terminal

/-- Actual score of the growth sequence is additive. -/
theorem candidateHtabSetGrowSeq_score {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetGrowSeq none post events) :
    ∃ (growEvents assignEvents searchEvents : List WorkEvent),
      events = growEvents ++ (assignEvents ++ searchEvents) ∧
      coeff.score (executionWork events) =
        coeff.score (executionWork growEvents) +
        coeff.score (executionWork assignEvents) +
        coeff.score (executionWork searchEvents) := by
  obtain ⟨_, _, growEvents, assignEvents, searchEvents, rfl, _, _, _⟩ :=
    candidateHtabSetGrowSeq_trace run
  refine ⟨growEvents, assignEvents, searchEvents, rfl, ?_⟩
  rw [executionWork_score_append, executionWork_score_append]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateHtabSetSideStores_trace
#print axioms BoundedTableExperiment.candidateHtabSetSideStorePair_trace
#print axioms BoundedTableExperiment.candidateHtabSetLink_outer
#print axioms BoundedTableExperiment.candidateHtabSetGrowth_trace
#print axioms BoundedTableExperiment.candidateHtabSetGrowSeq_trace
#print axioms BoundedTableExperiment.candidateHtabSetGrowSeq_score

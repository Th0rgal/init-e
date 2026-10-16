import InitECandidate.Runtime.HashFindInvariant32
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashFindTail : ProgHOL 64 :=
  .seq hashFindLoop (.return (.var .local (ofString "cap")))

/-- The lookup loop and capacity return are the original probe-index scope. -/
theorem source_htabFind_tail :
    sourceFindLocalScope (ofString "i") (sourceFunctionBody Guest.guestFn_htab_find_slot) =
      some (.dec (ofString "i") .one
        (.op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]]) hashFindTail) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_find_slot,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,
    sourceFindLocalScope,Option.orElse,hashFindTail,hashFindLoop,hashFindIteration,hashFindComparisonAddress,
    hashFindDecision,hashProbeOccupied,hashProbeStep]
  rfl

/-- The complete original lookup tail returns either an in-range match or
the capacity sentinel, within twice capacity source clocks. -/
theorem evaluate_hashFindTail32 {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindTail =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock := by
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant⟩ := evaluate_hashFindLoop32_capacity
    keys stride key capacity used empty bits power emptyInside keysAligned strideAligned keyAligned strideFits bounded
    state index valid budget
  unfold hashFindTail
  rw [evaluateHOLFiniteState_seq_line780,run]
  rcases outcome with normal | matched
  · obtain ⟨finalIndex,finalValid⟩ := finalInvariant normal
    rw [normal]
    have returned : evaluateHOLFiniteState post (.return (.var .local (ofString "cap"))) =
        (some (.returned (.val (.word capacity))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,finalValid.capLocal,shapeOfHOLExact]
    exact ⟨capacity,emptyLocalsHOLFinite post,returned,Nat.le_refl _,cost,remaining⟩
  · obtain ⟨found,inside,matched⟩ := matched
    rw [matched]
    exact ⟨found,post,rfl,Nat.le_of_lt inside,cost,remaining⟩

#print axioms source_htabFind_tail
#print axioms evaluate_hashFindTail32
end InitECandidate.Runtime

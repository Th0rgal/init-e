import InitECandidate.Runtime.StateRestoreRanked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Number of journal entries remaining above the caller's snapshot. -/
noncomputable def stateRestoreRank {F : Type} (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.globals.lookup (ofString "journal_n"), state.locals.lookup (ofString "snap") with
  | some (.val (.word count)), some (.val (.word snapshot)) => count.toNat - snapshot.toNat
  | _, _ => 0

theorem stateRestoreRank_of_bindings {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count snapshot : BitVec 64)
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (snap : state.locals.lookup (ofString "snap") = some (.val (.word snapshot))) :
    stateRestoreRank state = count.toNat - snapshot.toNat := by
  simp [stateRestoreRank,counter,snap]

theorem stateRestoreRank_dec_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    stateRestoreRank (decClockHOLFinite state) = stateRestoreRank state := rfl

/-- The actual source guard is true exactly when there are records to undo. -/
theorem eval_stateRestore_guard_rank {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count snapshot : BitVec 64)
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (snap : state.locals.lookup (ofString "snap") = some (.val (.word snapshot))) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) stateRestoreCondition =
      some (.val (.word (if stateRestoreRank state = 0 then 0 else 1))) := by
  rw [stateRestoreRank_of_bindings state count snapshot counter snap]
  simp [stateRestoreCondition,evalHOLFinite,evalHOLExact,counter,snap,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  split <;> split <;> simp_all <;> omega

/-- The concrete rank decreases after the original decrement, without wrapping. -/
theorem stateRestoreRank_decrement {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count snapshot : BitVec 64)
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (snap : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (active : 0 < stateRestoreRank state) :
    stateRestoreRank (setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state) < stateRestoreRank state := by
  have rank := stateRestoreRank_of_bindings state count snapshot counter snap
  have lower : snapshot.toNat < count.toNat := by omega
  have decrease := (stateRestore_rank_decreases count snapshot lower).2
  rw [stateRestoreRank_of_bindings _ (count - 1) snapshot]
  · omega
  · simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact snap

/-- The rank is bounded by the 64-bit counter, independently of host RAM. -/
theorem stateRestoreRank_lt_word_limit {F : Type} (state : PanSemStateFiniteExact 64 F) :
    stateRestoreRank state < 2 ^ 64 := by
  unfold stateRestoreRank
  split
  · rename_i count snapshot _ _
    have bound := count.isLt
    have sub := Nat.sub_le count.toNat snapshot.toNat
    omega
  · norm_num

theorem stateRestoreRank_total_budget {F : Type} (state : PanSemStateFiniteExact 64 F) :
    stateRestoreRank state * (2 ^ 72 + 1) ≤ 2 ^ 137 := by
  have rank := stateRestoreRank_lt_word_limit state
  have scaled := Nat.mul_le_mul_right (2 ^ 72 + 1) (Nat.le_of_lt rank)
  norm_num at scaled ⊢
  omega

#print axioms stateRestoreRank_lt_word_limit
#print axioms stateRestoreRank_total_budget
#print axioms stateRestoreRank_of_bindings
#print axioms stateRestoreRank_dec_clock
#print axioms eval_stateRestore_guard_rank
#print axioms stateRestoreRank_decrement
end InitECandidate.Runtime

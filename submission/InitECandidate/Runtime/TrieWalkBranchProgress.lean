import InitECandidate.Runtime.TrieWalkBranchAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkPositionRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "pos") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

/-- A branch node at the end of a key returns its value or fails; a normal
iteration therefore requires a strictly shorter current position. -/
theorem evaluate_trieWalk_branch_normal_before_end {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    index.toNat < length.toNat := by
  have different : index ≠ length := by
    intro equal
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "nlen"))) =
        some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,posLocal,nlenLocal,equal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_trieWalk_branch_branch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at run
    simp only [show ¬(1 : BitVec 64) = 0 by decide,if_false] at run
    have terminal := evaluate_trieWalk_branch_value_terminal state
    cases valueRun : evaluateHOLFiniteState state trieWalkBranchValueReturn with
    | mk result middle =>
      rw [valueRun] at terminal run
      cases result with
      | none => exact terminal rfl
      | some result => cases run
  by_contra bad
  exact different (BitVec.eq_of_toNat_eq (by omega))

/-- Normal branch traversal preserves the key-length invariant and strictly
reduces the remaining-nibble rank, without unsigned counter wraparound. -/
theorem evaluate_trieWalk_branch_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + 1))) ∧
    post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
    (index + 1).toNat ≤ length.toNat ∧
    trieWalkPositionRank length post < trieWalkPositionRank length state ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock := by
  have beforeEnd := evaluate_trieWalk_branch_normal_before_end state post index length posLocal nlenLocal bounded run
  have nextNat : (index + 1).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2 ^ 64; omega)]
    rfl
  obtain ⟨advanced,locals,memory,globals,clock⟩ := evaluate_trieWalk_branch_normal_position state post index posLocal run
  refine ⟨advanced,(locals (ofString "nlen") (by decide) (by decide)).trans nlenLocal,by rw [nextNat]; omega,?_,memory,globals,clock⟩
  simp only [trieWalkPositionRank,advanced,posLocal]
  rw [nextNat]
  omega

#print axioms evaluate_trieWalk_branch_normal_before_end
#print axioms evaluate_trieWalk_branch_progress
end InitECandidate.Runtime

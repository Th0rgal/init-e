import InitECandidate.Runtime.TrieWalkKindDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal kind dispatch can only reach an extension or branch child path.
Invalid nodes and leaves cannot fall through into another traversal step. -/
theorem evaluate_trieWalk_after_kind_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind : BitVec 64)
    (kindLocal : state.locals.lookup (ofString "k") = some (.val (.word kind)))
    (code : state.code = originalRuntimeCode) (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState state trieWalkAfterKind = (none,post)) :
    (kind = 2 ∧ evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) ∨
    (kind ≠ 0 ∧ kind ≠ 1 ∧ kind ≠ 2 ∧ evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) := by
  have condition (value : BitVec 64) : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "k")) (.const value)) =
      some (.val (.word (if kind = value then (1 : BitVec 64) else 0))) := by
    simp [evalHOLExact,kindLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_trieWalk_after_kind,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition 0] at run
  by_cases zero : kind = 0
  · simp only [if_pos zero,show ¬(1 : BitVec 64) = 0 by decide,if_false] at run
    have terminal := (evaluate_mptFail_call_bounded state (.const 2) 2 code nonzero
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact])).2.2
    cases callRun : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 2]) with
    | mk result middle =>
      rw [callRun] at terminal run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result => cases run
  · simp only [if_neg zero,if_true,evaluateHOLFiniteState_skip] at run
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition 1] at run
    by_cases one : kind = 1
    · simp only [if_pos one,show ¬(1 : BitVec 64) = 0 by decide,if_false] at run
      have terminal := evaluate_trieWalk_leaf_terminal state
      cases leafRun : evaluateHOLFiniteState state trieWalkLeafBranch with
      | mk result middle =>
        rw [leafRun] at terminal run
        cases result with
        | none => exact False.elim (terminal rfl)
        | some result => cases run
    · simp only [if_neg one,if_true,evaluateHOLFiniteState_skip] at run
      rw [evaluateHOLFiniteState_ite,condition 2] at run
      by_cases two : kind = 2
      · left
        exact ⟨two,by simpa only [if_pos two,show ¬(1 : BitVec 64) = 0 by decide,if_false] using run⟩
      · right
        exact ⟨zero,one,two,by simpa only [if_neg two,if_true] using run⟩

#print axioms evaluate_trieWalk_after_kind_normal
end InitECandidate.Runtime

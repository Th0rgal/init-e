import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.TrieWalkLeafBranchBound
import InitECandidate.Runtime.TrieWalkExtensionBranchBound
import InitECandidate.Runtime.TrieWalkBranchSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkAfterKind : ProgHOL 64 :=
  match trieWalkStep with | .dec _ _ _ body => body | _ => .skip

theorem source_trieWalk_after_kind : trieWalkAfterKind =
    .seq (.ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 2]) .skip)
      (.seq (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1)) trieWalkLeafBranch .skip)
        (.ite (.cmp .equal (.var .local (ofString "k")) (.const 2)) trieWalkExtensionBranch trieWalkBranchBranch)) := by
  simp only [trieWalkAfterKind,trieWalkLeafBranch,trieWalkExtensionBranch,trieWalkBranchBranch,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The exact original kind dispatch uses at most257 source ticks: invalid
nodes exit via mpt_fail, leaves return, extensions compare, and branch nodes
have no nested clock cost. No memory-success premise is required. -/
theorem evaluate_trieWalk_after_kind_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs index length kind : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (kindLocal : state.locals.lookup (ofString "k") = some (.val (.word kind)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (small : length.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkAfterKind;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have condition (value : BitVec 64) : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "k")) (.const value)) =
      some (.val (.word (if kind = value then (1 : BitVec 64) else 0))) := by
    simp [evalHOLExact,kindLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_trieWalk_after_kind,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition 0]
  by_cases zero : kind = 0
  · simp only [if_pos zero,show ¬(1 : BitVec 64) = 0 by decide,if_false]
    have facts := evaluate_mptFail_call_bounded state (.const 2) 2 code (by omega)
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact])
    cases callRun : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 2]) with
    | mk result post =>
      rw [callRun] at facts
      dsimp only at facts
      cases result with
      | none => exact False.elim (facts.2.2 rfl)
      | some result =>
        change state.clock ≤ post.clock + 257 ∧ post.clock ≤ state.clock ∧ some result ≠ some .timeOut
        exact ⟨by omega,by omega,facts.2.1⟩
  · simp only [if_neg zero,if_true,evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition 1]
    by_cases one : kind = 1
    · simp only [if_pos one,show ¬(1 : BitVec 64) = 0 by decide,if_false]
      have facts := evaluate_trieWalk_leaf_branch_bounded state node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded small ticks
      have terminal := evaluate_trieWalk_leaf_terminal state
      cases leafRun : evaluateHOLFiniteState state trieWalkLeafBranch with
      | mk result post =>
        rw [leafRun] at facts terminal
        dsimp only at facts terminal
        cases result with
        | none => exact False.elim (terminal rfl)
        | some result => exact facts
    · simp only [if_neg one,if_true,evaluateHOLFiniteState_skip]
      rw [evaluateHOLFiniteState_ite,condition 2]
      by_cases two : kind = 2
      · simp only [if_pos two,show ¬(1 : BitVec 64) = 0 by decide,if_false]
        exact evaluate_trieWalk_extension_branch_bounded state node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded small ticks
      · simp only [if_neg two,if_true]
        have facts := evaluate_trieWalk_branch_branch_clock state
        exact ⟨by omega,by omega,facts.2⟩

#print axioms source_trieWalk_after_kind
#print axioms evaluate_trieWalk_after_kind_bounded
end InitECandidate.Runtime

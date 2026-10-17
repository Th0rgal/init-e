import InitECandidate.Runtime.TrieWalkRegistryLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform source-clock ceiling for a traversal of at most 64 nibbles. -/
def trieWalkSourceBudget : Nat := 65 * 2^64 * 258

/-- The original complete function, including its initial declaration and
final empty return, obeys a uniform finite bound under the node registries. -/
theorem evaluate_trieWalk_registry_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (node nibs length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (small : length.toNat ≤ 64)
    (member : node = 0 ∨ node ∈ live) (registry : TrieWalkRegistry live extensions branches state)
    (nibbles : TrieNibbleRange state nibs length) (ticks : trieWalkSourceBudget ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trie_walk)
    state.clock ≤ evaluated.2.clock + trieWalkSourceBudget ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "pos") (.val (.word (0 : BitVec 64))) state
  have kept : ∀ name, name ≠ ofString "pos" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atNode := (kept (ofString "node") (by decide)).trans nodeLocal
  have atNibs := (kept (ofString "nibs") (by decide)).trans nibsLocal
  have atLength := (kept (ofString "nlen") (by decide)).trans nlenLocal
  have atPos : entered.locals.lookup (ofString "pos") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ceiling := trieWalkLoopRank_le entered 0 node length atPos atNode small
  have rankBudget : trieWalkLoopRank length entered * 258 ≤ trieWalkSourceBudget :=
    Nat.mul_le_mul_right 258 ceiling
  obtain ⟨result,post,run,cost,remaining,noTimeout,_⟩ := evaluate_trieWalk_registry_loop_bounded
    entered live extensions branches node nibs 0 length atNode atNibs atPos atLength code
      (by exact Nat.zero_le _) small member (registry.after_memory rfl) (nibbles.after_frame rfl rfl rfl)
      (by change trieWalkLoopRank length entered * 258 ≤ state.clock; omega)
  have loopBound : entered.clock ≤ (evaluateHOLFiniteState entered trieWalkLoop).2.clock + trieWalkSourceBudget ∧
      (evaluateHOLFiniteState entered trieWalkLoop).2.clock ≤ entered.clock ∧
      (evaluateHOLFiniteState entered trieWalkLoop).1 ≠ some .timeOut := by
    rw [run]
    dsimp only
    exact ⟨by omega,remaining,noTimeout⟩
  have sequence := evaluate_sequence_straight_bounded entered trieWalkLoop trieWalkEmptyReturn
    trieWalkSourceBudget loopBound rfl
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trie_walk) =
      (let output := evaluateHOLFiniteState entered (.seq trieWalkLoop trieWalkEmptyReturn)
       (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "pos",state.locals.lookup (ofString "pos"))})) := by
    rw [source_trieWalk_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    rfl
  rw [full]
  exact sequence

#print axioms evaluate_trieWalk_registry_body_bounded
end InitECandidate.Runtime

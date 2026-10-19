import InitECandidate.Runtime.WitnessResultAboveStack
import InitECandidate.Runtime.WitnessUnwindPrefixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual optional result-hash store preserves all retained parent tables
and saved allocation order, including store-access failures. -/
theorem witness_result_above_stack_after_hash_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength top node hash : BitVec 64) (persistentFloor lower : Nat)
    (valid : WitnessResultAboveStack s input inputLength top node persistentFloor lower)
    (atHash : s.locals.lookup (ofString "hash")=some (.val (.word hash)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word node)))
    (nodeBound : node.toNat≤33806089496) (code : s.code=originalRuntimeCode) :
    WitnessResultAboveStack (evaluateHOLFiniteState s witnessUnwindHashStore).2
      input inputLength top node persistentFloor lower := by
  rcases valid with zero | ⟨savedFrontier,above,stack⟩
  · exact Or.inl zero
  · have frames := witness_unwind_hash_store_frame s node hash atHash atResult code
    have metadata := evaluateHOLFiniteState_metadata s witnessUnwindHashStore
    have resultNat : (node+(24 : BitVec 64)).toNat=node.toNat+24 := by
      rw [BitVec.toNat_add]
      change (node.toNat+24)%2^64=node.toNat+24
      exact Nat.mod_eq_of_lt (by omega)
    refine Or.inr ⟨savedFrontier,above,stack.after_frame s _ input inputLength savedFrontier top persistentFloor lower
      metadata.2.1 savedFrontier lower (Nat.le_refl _) (Nat.le_refl _) ?_⟩
    intro watched lo hi
    apply frames.2.2 watched
    apply Or.inr
    intro same
    have equal := congrArg BitVec.toNat same
    rw [resultNat] at equal
    omega

#print axioms witness_result_above_stack_after_hash_store
end InitECandidate.Runtime

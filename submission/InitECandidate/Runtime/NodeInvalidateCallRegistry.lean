import InitECandidate.Runtime.NodeInvalidateRegistry
import InitECandidate.Runtime.OriginalNodeInvalidateCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original cache invalidation costs one call-entry tick and retains the
registry across both discarded calls and declaration continuations. -/
theorem evaluate_nodeInvalidate_call_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (argument : ExpHOL 64) (pointer : BitVec 64) (member : pointer ∈ live) (capacity : 32 ≤ size pointer)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word pointer)])
    (code : state.code = originalRuntimeCode) (clockNonzero : state.clock ≠ 0)
    (domain : ∀ offset ∈ ([8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_invalidate") [argument]) = (none,ready) ∧
      TrieWalkRegistry live extensions branches ready ∧ ready.clock = state.clock - 1 ∧ ready.locals = state.locals ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_invalidate") [argument] continuation) =
        (let result := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (0 : BitVec 64))) ready) continuation
         (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "nd",.val (.word pointer))
  let entry := callEntryStateHOLFinite state callee
  have binding : entry.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,registered,clock⟩ := evaluate_nodeInvalidate_registry entry live extensions branches size layout
    (registry.after_memory rfl) pointer member capacity binding domain
  have installed : state.code.lookup (ofString "node_invalidate") =
      some ([(ofString "nd",.one)],sourceFunctionBody Guest.guestFn_node_invalidate,.one) := by
    rw [code]; exact originalRuntimeCode_nodeInvalidate_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "node_invalidate") (ofString "nd")
    (sourceFunctionBody Guest.guestFn_node_invalidate) pointer installed
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "node_invalidate") [argument] [.val (.word pointer)]
    (sourceFunctionBody Guest.guestFn_node_invalidate) callee .one (.val (.word (0 : BitVec 64))) post args lookup clockNonzero body shape
  let ready := {post with locals := state.locals}
  refine ⟨ready,call,registered.after_memory rfl,clock,rfl,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "node_invalidate") .one .one [argument] [.val (.word pointer)]
    (sourceFunctionBody Guest.guestFn_node_invalidate) continuation callee (.val (.word (0 : BitVec 64)))
    args lookup clockNonzero body (Nat.le_of_eq clock) shape shape

#print axioms evaluate_nodeInvalidate_call_registry
end InitECandidate.Runtime

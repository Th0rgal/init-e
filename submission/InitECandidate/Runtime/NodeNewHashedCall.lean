import InitECandidate.Runtime.NodeNewHashedBody
import InitECandidate.Runtime.OriginalNodeNewHashedCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original hash-node call returns a fresh terminal node and
preserves caller locals and all memory below its allocation frontier. -/
theorem evaluate_nodeNewHashed_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer hash : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word hash)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 32).toNat ≤ 33806089496)
    (bounded : pointer.toNat + 32 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_hashed") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧ ready.memory pointer = .word 0 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 32))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → ready.memory address = state.memory address) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_new_hashed") [argument] continuation) =
        (let result := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation
         (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "hash",.val (.word hash))
  let entry := callEntryStateHOLFinite state callee
  have atHash : entry.locals.lookup (ofString "hash") = some (.val (.word hash)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,clock,kind,frontier,before⟩ := evaluate_nodeNewHashed_body entry pointer hash atHash heap code
    (by change state.clock - 1 ≠ 0; omega) request finishBound bounded domain
  have installed : state.code.lookup (ofString "node_new_hashed") =
      some ([(ofString "hash",.one)],sourceFunctionBody Guest.guestFn_node_new_hashed,.one) := by
    rw [code]; exact originalRuntimeCode_nodeNewHashed_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "node_new_hashed") (ofString "hash")
    (sourceFunctionBody Guest.guestFn_node_new_hashed) hash installed
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "node_new_hashed") [argument] [.val (.word hash)]
    (sourceFunctionBody Guest.guestFn_node_new_hashed) callee .one (.val (.word pointer)) post args lookup (by omega) body shape
  let ready := {post with locals := state.locals}
  refine ⟨ready,call,?_,rfl,kind,frontier,before,?_⟩
  · change post.clock = state.clock - 2
    change post.clock = (state.clock - 1) - 1 at clock
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "node_new_hashed") .one .one [argument] [.val (.word hash)]
      (sourceFunctionBody Guest.guestFn_node_new_hashed) continuation callee (.val (.word pointer))
      args lookup (by omega) body (by change post.clock ≤ entry.clock; rw [clock]; omega) shape shape

#print axioms evaluate_nodeNewHashed_call_and_declaration
end InitECandidate.Runtime

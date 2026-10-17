import InitECandidate.Runtime.NodeNewLeafBody
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.PanFourWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original leaf call returns a fresh terminal node and
preserves caller locals and all memory below its allocation frontier. -/
theorem evaluate_nodeNewLeaf_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nibArgument sizeArgument valueArgument lengthArgument : ExpHOL 64) (pointer nib nlen vptr vlen : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [nibArgument,sizeArgument,valueArgument,lengthArgument] = some [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (request : (64 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 64).toNat ≤ 33806089496)
    (bounded : pointer.toNat + 64 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧ ready.memory pointer = .word 1 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 64))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → ready.memory address = state.memory address) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument] continuation) =
        (let result := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation
         (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word nlen))).update (ofString "vptr",.val (.word vptr))).update (ofString "vlen",.val (.word vlen)))
  let entry := callEntryStateHOLFinite state callee
  have at_nib : entry.locals.lookup (ofString "nib") = some (.val (.word nib)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nlen" ≠ ofString "nib" by decide,show ofString "vptr" ≠ ofString "nib" by decide,show ofString "vlen" ≠ ofString "nib" by decide]
  have at_nlen : entry.locals.lookup (ofString "nlen") = some (.val (.word nlen)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vptr" ≠ ofString "nlen" by decide,show ofString "vlen" ≠ ofString "nlen" by decide]
  have at_vptr : entry.locals.lookup (ofString "vptr") = some (.val (.word vptr)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vlen" ≠ ofString "vptr" by decide]
  have at_vlen : entry.locals.lookup (ofString "vlen") = some (.val (.word vlen)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,clock,kind,frontier,before⟩ := evaluate_nodeNewLeaf_body entry pointer nib nlen vptr vlen
    at_nib at_nlen at_vptr at_vlen heap code
    (by change state.clock - 1 ≠ 0; omega) request finishBound bounded domain
  have installed : state.code.lookup (ofString "node_new_leaf") =
      some ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "vptr",.one),(ofString "vlen",.one)],sourceFunctionBody Guest.guestFn_node_new_leaf,.one) := by
    rw [code]; exact originalRuntimeCode_nodeNewLeaf_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (sourceFunctionBody Guest.guestFn_node_new_leaf)
    nib nlen vptr vlen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "node_new_leaf") [nibArgument,sizeArgument,valueArgument,lengthArgument] [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)]
    (sourceFunctionBody Guest.guestFn_node_new_leaf) callee .one (.val (.word pointer)) post args lookup (by omega) body shape
  let ready := {post with locals := state.locals}
  refine ⟨ready,call,?_,rfl,kind,frontier,before,?_⟩
  · change post.clock = state.clock - 2
    change post.clock = (state.clock - 1) - 1 at clock
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "node_new_leaf") .one .one [nibArgument,sizeArgument,valueArgument,lengthArgument] [.val (.word nib),.val (.word nlen),.val (.word vptr),.val (.word vlen)]
      (sourceFunctionBody Guest.guestFn_node_new_leaf) continuation callee (.val (.word pointer))
      args lookup (by omega) body (by change post.clock ≤ entry.clock; rw [clock]; omega) shape shape

#print axioms evaluate_nodeNewLeaf_call_and_declaration
end InitECandidate.Runtime

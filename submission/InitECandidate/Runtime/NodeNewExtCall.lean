import InitECandidate.Runtime.NodeNewExtBody
import InitECandidate.Runtime.OriginalNodeNewExtCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real extension-constructor call costs two source ticks, preserves all
memory below its allocation frontier, and binds the fresh parent pointer in
its actual declaration continuation. The old child is strictly smaller. -/
theorem evaluate_nodeNewExt_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nibArgument sizeArgument childArgument : ExpHOL 64) (pointer nib size child : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,childArgument] = some [.val (.word nib),.val (.word size),.val (.word child)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (request : (56 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 56).toNat ≤ 33806089496)
    (recordBound : pointer.toNat + 56 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (childBefore : child.toNat < pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ready.locals = state.locals ∧ ready.memory pointer = .word 2 ∧
      ready.memory (pointer + 40) = .word size ∧ ready.memory (pointer + 48) = .word child ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 56))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → ready.memory address = state.memory address) ∧
      (∀ next : BitVec 64, ready.memory (pointer + 40) = .word 0 → ready.memory (pointer + 48) = .word next → next.toNat < pointer.toNat) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word size))).update (ofString "child",.val (.word child))
  let entry := callEntryStateHOLFinite state callee
  have nibLocal : entry.locals.lookup (ofString "nib") = some (.val (.word nib)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "child" ≠ ofString "nib" from by decide,show ofString "nlen" ≠ ofString "nib" from by decide]
  have sizeLocal : entry.locals.lookup (ofString "nlen") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "child" ≠ ofString "nlen" from by decide]
  have childLocal : entry.locals.lookup (ofString "child") = some (.val (.word child)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,clock,kind,segment,childField,frontier,before,order⟩ := evaluate_nodeNewExt_body entry pointer nib size child
    nibLocal sizeLocal childLocal heap code (by change state.clock - 1 ≠ 0; omega) request finishBound recordBound domain childBefore
  have installed : state.code.lookup (ofString "node_new_ext") =
      some ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "child",.one)],sourceFunctionBody Guest.guestFn_node_new_ext,.one) := by
    rw [code]; exact originalRuntimeCode_nodeNewExt_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "node_new_ext") (ofString "nib") (ofString "nlen") (ofString "child")
    (sourceFunctionBody Guest.guestFn_node_new_ext) nib size child (by decide) (by decide) (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have nonzero : state.clock ≠ 0 := by omega
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]
    [.val (.word nib),.val (.word size),.val (.word child)] (sourceFunctionBody Guest.guestFn_node_new_ext) callee .one
    (.val (.word pointer)) post args lookup nonzero body shapeOk
  let ready := {post with locals := state.locals}
  refine ⟨ready,call,?_,rfl,kind,segment,childField,frontier,before,order,?_⟩
  · change post.clock = state.clock - 2
    change post.clock = (state.clock - 1) - 1 at clock
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "node_new_ext") .one .one
      [nibArgument,sizeArgument,childArgument] [.val (.word nib),.val (.word size),.val (.word child)]
      (sourceFunctionBody Guest.guestFn_node_new_ext) continuation callee (.val (.word pointer))
      args lookup nonzero body (by change post.clock ≤ entry.clock; rw [clock]; omega) shapeOk shapeOk

#print axioms evaluate_nodeNewExt_call_and_declaration
end InitECandidate.Runtime

import InitECandidate.Runtime.NodeNewBranchBody
import InitECandidate.Runtime.OriginalNodeNewBranchCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original zero-argument branch constructor call and declaration
continuation expose the fresh pointer, with all child words initialized null. -/
theorem evaluate_nodeNewBranch_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 179 ≤ state.clock)
    (request : (176 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 176).toNat ≤ 33806089496)
    (bounded : pointer.toNat + 176 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_branch") []) = (none,ready) ∧
      state.clock ≤ ready.clock + 179 ∧ ready.clock ≤ state.clock ∧ ready.locals = state.locals ∧
      ready.memory pointer = .word 3 ∧
      (∀ slot : Nat, slot < 16 → ready.memory (branchChildAddress pointer slot) = .word 0) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 176))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → ready.memory address = state.memory address) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "node_new_branch") [] continuation) =
        (let result := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) ready) continuation
         (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (name,state.locals.lookup name)}))) := by
  let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  obtain ⟨post,body,cost,remaining,kind,children,frontier,before⟩ := evaluate_nodeNewBranch_body
    entry pointer heap code (by change 178 ≤ state.clock - 1; omega) request finishBound bounded aligned wordDomain byteDomain
  have installed : state.code.lookup (ofString "node_new_branch") =
      some ([],sourceFunctionBody Guest.guestFn_node_new_branch,.one) := by
    rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch) installed
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [] = some [] := rfl
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "node_new_branch") [] []
    (sourceFunctionBody Guest.guestFn_node_new_branch) HolFiniteMapExact.empty .one (.val (.word pointer)) post
    args lookup (by omega) body shape
  let ready := {post with locals := state.locals}
  refine ⟨ready,call,?_,?_,rfl,kind,children,frontier,before,?_⟩
  · change state.clock ≤ post.clock + 179
    change state.clock - 1 ≤ post.clock + 178 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "node_new_branch") .one .one [] []
      (sourceFunctionBody Guest.guestFn_node_new_branch) continuation HolFiniteMapExact.empty (.val (.word pointer))
      args lookup (by omega) body remaining shape shape

#print axioms evaluate_nodeNewBranch_call_and_declaration
end InitECandidate.Runtime

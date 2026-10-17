import InitECandidate.Runtime.NodeNewBranchInitialize
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_nodeNewBranch_body : sourceFunctionBody Guest.guestFn_node_new_branch =
    .decCall (ofString "nd") .one (ofString "alloc") [.const 176] nodeNewBranchInitialize := by
  simp only [nodeNewBranchInitialize,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original branch constructor allocates a fresh zero-child
record, changes its kind to 3, and preserves all memory below the old heap. -/
theorem evaluate_nodeNewBranch_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 178 ≤ state.clock)
    (request : (176 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 176).toNat ≤ 33806089496)
    (bounded : pointer.toNat + 176 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_branch) =
      (some (.returned (.val (.word pointer))),post) ∧
      state.clock ≤ post.clock + 178 ∧ post.clock ≤ state.clock ∧
      post.memory pointer = .word 3 ∧
      (∀ slot : Nat, slot < 16 → post.memory (branchChildAddress pointer slot) = .word 0) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 176))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 176] =
      some [.val (.word (176 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨ready,_,clock,memory,locals,postCode,addresses,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 176) pointer 176 args code (by omega) heap request finishBound
  let entered := setVarHOLFinite (ofString "nd") (.val (.word pointer)) ready
  have atNd : entered.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryCode : entered.code = originalRuntimeCode := postCode.trans code
  have entryTicks : 177 ≤ entered.clock := by change 177 ≤ ready.clock; omega
  obtain ⟨output,initialization,cost,remaining,kind,children,postGlobals,_,_,_,before⟩ :=
    evaluate_nodeNewBranch_initialize entered pointer atNd entryCode entryTicks bounded aligned
      (by intro offset small; change ready.memaddrs _; rw [addresses]; exact wordDomain offset small)
      (by intro offset small; change ready.memaddrs _; rw [addresses]; exact byteDomain offset small)
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "nd",state.locals.lookup (ofString "nd"))}
  refine ⟨post,?_,?_,?_,kind,children,?_,?_⟩
  · rw [source_nodeNewBranch_body,declaration (ofString "nd") nodeNewBranchInitialize]
    change (let result := evaluateHOLFiniteState entered nodeNewBranchInitialize; _) = _
    rw [initialization]
  · change state.clock ≤ output.clock + 178
    change ready.clock ≤ output.clock + 177 at cost
    omega
  · change output.clock ≤ state.clock
    change output.clock ≤ ready.clock at remaining
    omega
  · change output.globals.lookup (ofString "heap_ptr") = _
    rw [postGlobals]
    change ready.globals.lookup (ofString "heap_ptr") = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro address below
    exact (before address below).trans (congrFun memory address)

#print axioms source_nodeNewBranch_body
#print axioms evaluate_nodeNewBranch_body
end InitECandidate.Runtime

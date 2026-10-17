import InitECandidate.Runtime.NodeNewLeafStores
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_nodeNewLeaf_body : sourceFunctionBody Guest.guestFn_node_new_leaf =
    .decCall (ofString "nd") .one (ofString "alloc") [.const 64] nodeNewLeafStores := by
  simp only [nodeNewLeafStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Successful original leaf construction establishes terminal kind 1
while preserving every memory cell below the allocation frontier. -/
theorem evaluate_nodeNewLeaf_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib nlen vptr vlen : BitVec 64)
    (nibLocal : state.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (vptrLocal : state.locals.lookup (ofString "vptr") = some (.val (.word vptr)))
    (vlenLocal : state.locals.lookup (ofString "vlen") = some (.val (.word vlen)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (request : (64 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 64).toNat ≤ 33806089496)
    (recordBound : pointer.toNat + 64 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
 :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_leaf) = (some (.returned (.val (.word pointer))),post) ∧
      post.clock = state.clock - 1 ∧ post.memory pointer = .word 1 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 64))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 64] =
      some [.val (.word (64 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨ready,_,ticks,memory,locals,_,addresses,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 64) pointer 64 args code clock heap request finishBound
  let entered := setVarHOLFinite (ofString "nd") (.val (.word pointer)) ready
  have atNd : entered.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have kept : ∀ name, name ≠ ofString "nd" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have stores := evaluate_nodeNewLeaf_stores entered pointer nib nlen vptr vlen atNd
    ((kept _ (by decide)).trans nibLocal)
    ((kept _ (by decide)).trans nlenLocal)
    ((kept _ (by decide)).trans vptrLocal)
    ((kept _ (by decide)).trans vlenLocal)
    (by intro offset member; change ready.memaddrs _; rw [addresses]; exact domain offset member)
  let post := {nodeNewLeafStoresPost entered pointer nib nlen vptr vlen with locals := HolFiniteMapExact.resVarEq (nodeNewLeafStoresPost entered pointer nib nlen vptr vlen).locals (ofString "nd",state.locals.lookup (ofString "nd"))}
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_leaf) =
      (some (.returned (.val (.word pointer))),post) := by
    rw [source_nodeNewLeaf_body,declaration (ofString "nd") nodeNewLeafStores]
    change (let output := evaluateHOLFiniteState entered nodeNewLeafStores; _) = _
    rw [stores]
  have kind := nodeNewLeafStoresPost_kind entered pointer nib nlen vptr vlen
  refine ⟨post,full,ticks,kind,?_,?_⟩
  · change ready.globals.lookup (ofString "heap_ptr") = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro address before
    exact (nodeNewLeafStoresPost_before entered pointer nib nlen vptr vlen recordBound address before).trans (congrFun memory address)

#print axioms source_nodeNewLeaf_body
#print axioms evaluate_nodeNewLeaf_body
end InitECandidate.Runtime

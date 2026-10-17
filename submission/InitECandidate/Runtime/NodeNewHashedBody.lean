import InitECandidate.Runtime.NodeNewHashedStores
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_nodeNewHashed_body : sourceFunctionBody Guest.guestFn_node_new_hashed =
    .decCall (ofString "nd") .one (ofString "alloc") [.const 32] nodeNewHashedStores := by
  simp only [nodeNewHashedStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Successful original hash-node construction establishes terminal kind 0
while preserving every memory cell below the allocation frontier. -/
theorem evaluate_nodeNewHashed_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 32).toNat ≤ 33806089496)
    (recordBound : pointer.toNat + 32 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
 :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_hashed) = (some (.returned (.val (.word pointer))),post) ∧
      post.clock = state.clock - 1 ∧ post.memory pointer = .word 0 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 32))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 32] =
      some [.val (.word (32 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨ready,_,ticks,memory,locals,_,addresses,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 32) pointer 32 args code clock heap request finishBound
  let entered := setVarHOLFinite (ofString "nd") (.val (.word pointer)) ready
  have atNd : entered.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have kept : ∀ name, name ≠ ofString "nd" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have stores := evaluate_nodeNewHashed_stores entered pointer hash atNd
    ((kept _ (by decide)).trans hashLocal)
    (by intro offset member; change ready.memaddrs _; rw [addresses]; exact domain offset member)
  let post := {nodeNewHashedStoresPost entered pointer hash with locals := HolFiniteMapExact.resVarEq (nodeNewHashedStoresPost entered pointer hash).locals (ofString "nd",state.locals.lookup (ofString "nd"))}
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_hashed) =
      (some (.returned (.val (.word pointer))),post) := by
    rw [source_nodeNewHashed_body,declaration (ofString "nd") nodeNewHashedStores]
    change (let output := evaluateHOLFiniteState entered nodeNewHashedStores; _) = _
    rw [stores]
  have kind := nodeNewHashedStoresPost_kind entered pointer hash
  refine ⟨post,full,ticks,kind,?_,?_⟩
  · change ready.globals.lookup (ofString "heap_ptr") = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro address before
    exact (nodeNewHashedStoresPost_before entered pointer hash recordBound address before).trans (congrFun memory address)

#print axioms source_nodeNewHashed_body
#print axioms evaluate_nodeNewHashed_body
end InitECandidate.Runtime

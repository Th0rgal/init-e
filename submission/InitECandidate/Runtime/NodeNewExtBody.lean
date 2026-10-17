import InitECandidate.Runtime.NodeNewExtStoreFields
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_nodeNewExt_body : sourceFunctionBody Guest.guestFn_node_new_ext =
    .decCall (ofString "nd") .one (ofString "alloc") [.const 56] nodeNewExtStores := by
  simp only [nodeNewExtStores,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Successful execution of the original extension constructor. The child
must already lie below the allocation frontier; the new parent then preserves
all earlier memory and records a strictly smaller child, even at zero length. -/
theorem evaluate_nodeNewExt_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer nib size child : BitVec 64)
    (nibLocal : state.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (sizeLocal : state.locals.lookup (ofString "nlen") = some (.val (.word size)))
    (childLocal : state.locals.lookup (ofString "child") = some (.val (.word child)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (request : (56 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 56).toNat ≤ 33806089496)
    (recordBound : pointer.toNat + 56 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (childBefore : child.toNat < pointer.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_ext) = (some (.returned (.val (.word pointer))),post) ∧
      post.clock = state.clock - 1 ∧ post.memory pointer = .word 2 ∧
      post.memory (pointer + 40) = .word size ∧ post.memory (pointer + 48) = .word child ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 56))) ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) ∧
      (∀ next : BitVec 64, post.memory (pointer + 40) = .word 0 →
        post.memory (pointer + 48) = .word next → next.toNat < pointer.toNat) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 56] =
      some [.val (.word (56 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨ready,_,ticks,memory,locals,_,addresses,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 56) pointer 56 args code clock heap request finishBound
  let entered := setVarHOLFinite (ofString "nd") (.val (.word pointer)) ready
  have atNd : entered.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have kept : ∀ name, name ≠ ofString "nd" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have stores := evaluate_nodeNewExt_stores entered pointer nib size child atNd
    ((kept _ (by decide)).trans nibLocal) ((kept _ (by decide)).trans sizeLocal) ((kept _ (by decide)).trans childLocal)
    (by intro offset member; change ready.memaddrs _; rw [addresses]; exact domain offset member)
  let post := {nodeNewExtStoresPost entered pointer nib size child with locals := HolFiniteMapExact.resVarEq (nodeNewExtStoresPost entered pointer nib size child).locals (ofString "nd",state.locals.lookup (ofString "nd"))}
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_node_new_ext) =
      (some (.returned (.val (.word pointer))),post) := by
    rw [source_nodeNewExt_body,declaration (ofString "nd") nodeNewExtStores]
    change (let output := evaluateHOLFiniteState entered nodeNewExtStores; _) = _
    rw [stores]
  have fields := nodeNewExtStoresPost_fields entered pointer nib size child
  have childField : post.memory (pointer + 48) = .word child := fields.2.2.2
  refine ⟨post,full,ticks,fields.1,fields.2.2.1,childField,?_,?_,?_⟩
  · change ready.globals.lookup (ofString "heap_ptr") = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro address before
    exact (nodeNewExtStoresPost_before entered pointer nib size child recordBound address before).trans (congrFun memory address)
  · intro next _ loaded
    have equal : child = next := HolWordLab.word.inj (childField.symm.trans loaded)
    simpa only [← equal] using childBefore

#print axioms source_nodeNewExt_body
#print axioms evaluate_nodeNewExt_body
end InitECandidate.Runtime

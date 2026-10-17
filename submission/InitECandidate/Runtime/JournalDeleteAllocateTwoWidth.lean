import InitECandidate.Runtime.HashTableReadyAllocDeclaration
import InitECandidate.Runtime.JournalDeleteSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original key-copy allocation enters the journal copy body with its
returned pointer, advanced heap frontier and preserved non-heap globals. -/
theorem HashTableReady.jdel_allocate_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (clock : state.clock ≠ 0) (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state) :
    ∃ post, HashTableReady keyLength table keys stride capacity used values order orderPos items bits (allocationEnd pointer keyLength) post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post ∧
      post.locals.lookup (ofString "kc") = some (.val (.word pointer)) ∧
      (∀ name, name ≠ ofString "kc" → post.locals.lookup name = state.locals.lookup name) ∧
      (∀ name, name ≠ ofString "heap_ptr" → post.globals.lookup name = state.globals.lookup name) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32) =
        (let output := evaluateHOLFiniteState post journalDeleteCopy32;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc")))})) := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "klen")] = some [.val (.word keyLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,klen]
  obtain ⟨allocated,run,allocatedReady,ticks,memory,locals,code,domain,_,endian,globals,decl⟩ :=
    ready.alloc_declaration state keyLength table keys stride capacity used values order orderPos items bits pointer keyLength
      (.var .local (ofString "klen")) arguments clock request
  obtain ⟨checked,checkedRun,checkedReady,_,_,_,_,_,_,_,_,_⟩ :=
    otherReady.alloc_declaration state otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer keyLength
      (.var .local (ofString "klen")) arguments clock request
  have same : allocated = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have allocatedOther : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) allocated := by
    rw [same]
    exact checkedReady
  let post := setVarHOLFinite (ofString "kc") (.val (.word pointer)) allocated
  refine ⟨post,allocatedReady.after_read allocated post keyLength table keys stride capacity used values order orderPos items bits
    (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,
    allocatedOther.after_read allocated post otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,?_,?_,?_,ticks,memory,code,domain,endian,decl (ofString "kc") journalDeleteCopy32⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  · intro name different
    change allocated.globals.lookup name = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms HashTableReady.jdel_allocate_with_other
end InitECandidate.Runtime

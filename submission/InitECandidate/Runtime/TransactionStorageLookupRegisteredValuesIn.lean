import InitECandidate.Runtime.TransactionStorageInnerScopeAllRequestsRegisteredValuesIn
import InitECandidate.Runtime.HashGetCallValueProperty
import InitECandidate.Runtime.TransactionRegistryHeapExists
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateStorageLookupScope : ProgHOL 64 :=
  .decCall (ofString "m") (.comb [.one,.one]) (ofString "htab_get")
    [.var .local (ofString "outer"),.var .local (ofString "addr")] stateStorageInnerScope

theorem source_setStorage_lookup_scope :
    stateInitSpineDrop 3 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageLookupScope := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual outer lookup selects a registered, typed inner table. Both
subsequent branches retain that pointer invariant for later storage operations. -/
theorem TransactionRegistryWorld.storage_lookup_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count outer addr key a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables) (targetsSubset : targets ⊆ tables)
    (typed : ∀ inner ∈ targets, widths inner = 32 ∧ inner ∉ watched)
    (outerWatched : outer ∈ watched)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 77 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageLookupScope = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 77 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ nextWidths nextTables nextTargets nextCount,
        TransactionRegistryWorld nextWidths nextTables fieldPointer ts journal snapshot nextCount post ∧
        watched ⊆ nextTables ∧ nextTargets ⊆ nextTables ∧
        (∀ inner ∈ nextTargets, nextWidths inner = 32 ∧ inner ∉ watched) ∧
        (∀ other ∈ watched, HashTableValuesIn other nextTargets post) ∧
        JournalSavedValuesIn journal nextCount.toNat watched nextTargets post) := by
  obtain ⟨op,keys,stride,capacity,used,values,order,reverse,items,bits,logicalReady,_,_⟩ := valid.journalWorld.world.ready outer (watchedSubset outerWatched)
  have ready := logicalReady.after_read _ state (widths outer) outer keys stride capacity used values order reverse items bits op rfl rfl rfl rfl rfl
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "outer"),.var .local (ofString "addr")] = some [.val (.word outer),.val (.word addr)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,outerLocal,addrLocal]
  obtain ⟨present,inner,middle,_,_,lookupCost,lookupRemaining,locals,memory,globals,code,domain,endian,innerTarget,declaration⟩ :=
    ready.live.arrays.get_value_property state (widths outer) outer keys stride capacity used values order reverse items addr bits
      (fun inner => inner ∈ targets) (valid.journalWorld.supported outer (watchedSubset outerWatched))
      _ _ args addrAligned addrWords addrBytes
      (registered outer outerWatched capacity used values ready.live.arrays.cell16 ready.live.arrays.cell48 ready.live.arrays.cell40) (by omega)
  let entered := setVarHOLFinite (ofString "m") (.rStruct [.val (.word present),.val (.word inner)]) middle
  have midValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := valid.after_read memory globals code domain endian
  have other : ∀ name, name ≠ ofString "m" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have mLocal : entered.locals.lookup (ofString "m") = some (.rStruct [.val (.word present),.val (.word inner)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨pointer,heap,_,_,_⟩ := midValid.heap_exists
  have selectedWidth : (if present = 0 then (32 : BitVec 64) else widths inner).toNat = 32 := by
    split
    · rfl
    · rename_i nonzero
      rw [(typed inner (innerTarget nonzero)).1]
      rfl
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := midValid.storage_inner_scope_all_requests_registered_values_in entered widths tables
    fieldPointer ts journal snapshot count pointer outer addr key a b c d present inner (watchedSubset outerWatched)
    (fun nonzero => targetsSubset (innerTarget nonzero))
    ((other _ (by decide)).trans outerLocal) ((other _ (by decide)).trans addrLocal)
    ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans valueLocal) mLocal heap addrAligned keyAligned
    (by simpa only [entered,setVarHOLFinite,domain] using addrWords) (by simpa only [entered,setVarHOLFinite,domain] using addrBytes)
    (by simpa only [selectedWidth,entered,setVarHOLFinite,domain] using keyWords) (by simpa only [selectedWidth,entered,setVarHOLFinite,domain] using keyBytes)
    watched targets watchedSubset (fun other belongs => (registered other belongs).after_read memory domain endian)
    (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact congrFun memory _))
    (fun nonzero belongs => False.elim ((typed inner (innerTarget nonzero)).2 belongs)) (by change 2 ^ 76 + 19 ≤ middle.clock; omega)
  have full : evaluateHOLFiniteState state stateStorageLookupScope =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "m",state.locals.lookup (ofString "m"))}) := by
    rw [stateStorageLookupScope,declaration,run]
  refine ⟨result,_,full,?_,?_,noTimeout,?_⟩
  · change state.clock ≤ post.clock + 2 ^ 77
    change middle.clock ≤ post.clock + (2 ^ 76 + 19) at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ middle.clock at remaining
    omega
  · intro value success
    have joint := preserved value success
    by_cases missing : present = 0
    · rw [if_pos missing] at joint
      have fresh : pointer ∉ tables := by
        intro belongs
        have bound := midValid.journalWorld.world.registered_header_before_frontier pointer pointer belongs heap
        omega
      have nextTyped : ∀ actual ∈ insert pointer targets, withTableWidth widths pointer 32 actual = 32 ∧ actual ∉ watched := by
        intro actual belongs
        rcases Set.mem_insert_iff.mp belongs with same | old
        · subst actual
          exact ⟨by simp [withTableWidth],fun member => fresh (watchedSubset member)⟩
        · have different : actual ≠ pointer := by intro same; subst actual; exact fresh (targetsSubset old)
          exact ⟨by simpa [withTableWidth,different] using (typed actual old).1,(typed actual old).2⟩
      exact ⟨withTableWidth widths pointer 32,insert pointer tables,insert pointer targets,((count + 1) + 1),
        joint.1.after_read rfl rfl rfl rfl rfl,
        (fun actual belongs => Set.mem_insert_of_mem pointer (watchedSubset belongs)),
        (by intro actual belongs; rcases Set.mem_insert_iff.mp belongs with same | old; exact same ▸ Set.mem_insert pointer tables; exact Set.mem_insert_of_mem pointer (targetsSubset old)),
        nextTyped,(fun other belongs => (joint.2.1 other belongs).after_read rfl rfl rfl),
        joint.2.2.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩
    · rw [if_neg missing] at joint
      exact ⟨widths,tables,targets,count + 1,joint.1.after_read rfl rfl rfl rfl rfl,watchedSubset,targetsSubset,typed,
        (fun other belongs => (joint.2.1 other belongs).after_read rfl rfl rfl),
        joint.2.2.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩

#print axioms source_setStorage_lookup_scope
#print axioms TransactionRegistryWorld.storage_lookup_registered_values_in
end InitECandidate.Runtime

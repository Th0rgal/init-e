import InitECandidate.Runtime.HashGrowUsedAllocation32
import InitECandidate.Runtime.HashGrowOrderSafePlanWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabGrow_used_allocation_width_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride : BitVec 64) (bits : Nat) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 4 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word keyLength)
    (strideField : state.memory (table + 8) = .word stride)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (ncapLocal : state.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2))))
    (nkeysLocal : state.locals.lookup (ofString "nkeys") = some (.val (.word pointer)))
    (nvalsLocal : state.locals.lookup (ofString "nvals") = some (.val (.word (htabGrowValues pointer capacity stride))))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word (htabGrowUsed pointer capacity stride)))) :
    ∃ ready, evaluateHOLFiniteState state (hashGrowUsedAllocation continuation) =
      (let output := evaluateHOLFiniteState ready continuation;
       (output.1,{output.2 with locals := (restoreGrowthLocals state.locals [ofString "nused",ofString "norder",ofString "norder_pos"] output.2.locals)})) ∧
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) 0 (bits + 1) ready ∧
      state.clock ≤ ready.clock + (capacity * 2).toNat + 4 ∧ ready.clock ≤ state.clock ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      (∀ name, name ∉ [ofString "nused",ofString "norder",ofString "norder_pos"] → ready.locals.lookup name = state.locals.lookup name) ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        ready.memory watched = state.memory watched) := by
  have safe := safePlan
  obtain ⟨_,_,_,_,guard,finish,_⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "ncap")] = some [.val (.word (capacity * 2))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ncapLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,clock,memory,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state _ (htabGrowUsed pointer capacity stride) (capacity * 2) arguments code (by omega) heap guard finish
  let entered := setVarHOLFinite (ofString "nused") (.val (.word (htabGrowUsed pointer capacity stride))) allocated
  have other : ∀ name, name ≠ ofString "nused" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have boundLocal : entered.locals.lookup (ofString "nused") = some (.val (.word (htabGrowUsed pointer capacity stride))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (htabGrowOrder pointer capacity stride))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,htabGrowOrder]
  have domainAfter : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → entered.memaddrs address := by
    change ∀ address : BitVec 64, _ → _ → allocated.memaddrs address
    rw [addresses]; exact domain
  obtain ⟨ready,run,valid,cost,remaining,lastCode,lastAddresses,lastEndian,lastOther,lastFrame⟩ :=
    evaluate_htabGrow_order_allocation_width_safe_plan entered keyLength table pointer capacity stride bits continuation (postCode.trans code) power
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
      (by change (capacity * 2).toNat + 3 ≤ allocated.clock; omega) domainAfter
      (by change allocated.memory _ = _; rw [memory]; exact keyField)
      (by change allocated.memory _ = _; rw [memory]; exact strideField)
      ((other (ofString "t") (by decide)).trans tableLocal)
      ((other (ofString "ncap") (by decide)).trans ncapLocal)
      ((other (ofString "nkeys") (by decide)).trans nkeysLocal)
      ((other (ofString "nvals") (by decide)).trans nvalsLocal)
      boundLocal
      nextHeap
  have saved0 : entered.locals.lookup (ofString "norder") = state.locals.lookup (ofString "norder") := other _ (by decide)
  have saved1 : entered.locals.lookup (ofString "norder_pos") = state.locals.lookup (ofString "norder_pos") := other _ (by decide)
  unfold hashGrowUsedAllocation
  rw [decl]
  change ∃ ready, (let output := evaluateHOLFiniteState entered (hashGrowOrderAllocation continuation); _) = _ ∧ _
  rw [run]
  refine ⟨ready,?_,valid,?_,?_,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_,?_⟩
  · dsimp only
    simp only [restoreGrowthLocals,saved0,saved1]
  · change allocated.clock ≤ ready.clock + (capacity * 2).toNat + 3 at cost
    omega
  · change ready.clock ≤ allocated.clock at remaining
    omega
  · intro name outside
    have neCurrent : name ≠ ofString "nused" := by intro same; apply outside; simp [same]
    have outsideRest : name ∉ [ofString "norder",ofString "norder_pos"] := by
      intro member
      apply outside
      exact List.mem_cons_of_mem _ member
    exact (lastOther name outsideRest).trans (other name neCurrent)
  · intro watched lower upper
    have preserved := lastFrame watched lower upper
    rw [preserved]
    change allocated.memory watched = state.memory watched
    rw [memory]

#print axioms evaluate_htabGrow_used_allocation_width_safe_plan
end InitECandidate.Runtime

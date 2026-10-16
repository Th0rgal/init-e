import InitECandidate.Runtime.HashGrowOrderAllocation32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowUsedAllocation (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "nused") .one (ofString "alloc") [.var .local (ofString "ncap")] (hashGrowOrderAllocation continuation)

/-- The final 3 original growth allocations compose initialization with their actual scopes. -/
theorem evaluate_htabGrow_used_allocation32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity stride : BitVec 64) (bits : Nat) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : 32 ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (heapBudget : pointer.toNat + 162 * capacity.toNat + 35 ≤ 33806089496)
    (ticks : (capacity * 2).toNat + 4 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word (32 : BitVec 64))
    (strideField : state.memory (table + 8) = .word stride)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (ncapLocal : state.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2))))
    (nkeysLocal : state.locals.lookup (ofString "nkeys") = some (.val (.word pointer)))
    (nvalsLocal : state.locals.lookup (ofString "nvals") = some (.val (.word (htabGrowValues pointer capacity stride))))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word (htabGrowUsed pointer capacity stride)))) :
    ∃ ready, evaluateHOLFiniteState state (hashGrowUsedAllocation continuation) =
      (let output := evaluateHOLFiniteState ready continuation;
       (output.1,{output.2 with locals := (restoreGrowthLocals state.locals [ofString "nused",ofString "norder",ofString "norder_pos"] output.2.locals)})) ∧
      HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) 0 (bits + 1) ready ∧
      state.clock ≤ ready.clock + (capacity * 2).toNat + 4 ∧ ready.clock ≤ state.clock ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ∀ name, name ∉ [ofString "nused",ofString "norder",ofString "norder_pos"] → ready.locals.lookup name = state.locals.lookup name := by
  have safe := (htabGrow_allocation_plan_safe pointer capacity stride strideBound heapBudget).2.1
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
  obtain ⟨ready,run,valid,cost,remaining,lastCode,lastAddresses,lastEndian,lastOther⟩ :=
    evaluate_htabGrow_order_allocation32 entered table pointer capacity stride bits continuation (postCode.trans code) power
      strideAligned fits strideBound pointerAligned headerBefore heapBudget
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
  refine ⟨ready,?_,valid,?_,?_,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
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

theorem source_htabGrow_used_allocation :
    sourceFindDeclarationCallScope (ofString "nused") (sourceFunctionBody Guest.guestFn_htab_grow) =
      some (hashGrowUsedAllocation (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_htabGrow_used_allocation
#print axioms evaluate_htabGrow_used_allocation32
end InitECandidate.Runtime

import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.HashNewUsedAllocation
import InitECandidate.Runtime.HashNewZeroHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabNew_used_allocation_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 4 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (htabNewUsed table keyLength capacity))))
    (safe : AllocationPlanSafe (htabNewUsed table keyLength capacity) [capacity,capacity * 8,capacity * 8])
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48)) (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewUsedAllocation = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 4 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) ∧ HeapGlobalsFrame state post := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "cap")] =
        some [.val (.word capacity)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal]
  obtain ⟨allocated,_,clock,_,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state _ (htabNewUsed table keyLength capacity) capacity arguments code
      (by omega) heap guard finish
  let entered := setVarHOLFinite (ofString "used") (.val (.word (htabNewUsed table keyLength capacity))) allocated
  have nt : ofString "used" ≠ ofString "t" := by decide
  have nc : ofString "used" ≠ ofString "cap" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,locals] using tableLocal
  have c : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have u : entered.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have updated : entered.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd (htabNewUsed table keyLength capacity) capacity))) := by
    change allocated.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,lastHeap,lastFrame⟩ :=
    evaluate_htabNew_zero_tail_heap_frame entered (allocationEnd (htabNewUsed table keyLength capacity) capacity)
      table keyLength capacity (postCode.trans code) (by change capacity.toNat + 3 ≤ allocated.clock; omega)
      updated restSafe keyBound tableAligned budget t u c
      (by change allocated.memaddrs _; rw [addresses]; exact domain48)
      (by change allocated.memaddrs _; rw [addresses]; exact domain56)
      (by change allocated.memaddrs _; rw [addresses]; exact domain64)
      (by simpa [entered,setVarHOLFinite,addresses] using wordDomain)
      (by simpa [entered,setVarHOLFinite,addresses] using byteDomain)
  have enteredClock : entered.clock = state.clock - 1 := clock
  unfold htabNewUsedAllocation
  rw [decl]
  change (∃ result, (let output := evaluateHOLFiniteState entered htabNewUsedBody; _) = _ ∧ _)
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 4; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap,?_⟩
  intro watched notHeap
  exact (lastFrame watched notHeap).trans (by
    change allocated.globals.lookup watched = state.globals.lookup watched
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap])

#print axioms evaluate_htabNew_used_allocation_heap_frame
end InitECandidate.Runtime

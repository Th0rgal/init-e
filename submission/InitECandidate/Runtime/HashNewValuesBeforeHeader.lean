import InitECandidate.Runtime.HashNewValuesAllocation
import InitECandidate.Runtime.HashNewUsedBeforeHeader
import InitECandidate.Runtime.HashNewMemoryBeforeHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The values allocation and the remaining original constructor return an
empty table within capacity+5 source clocks. -/
theorem evaluate_htabNew_values_allocation_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 5 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (htabNewValues table keyLength capacity))))
    (safe : AllocationPlanSafe (htabNewValues table keyLength capacity)
      [capacity * 8,capacity,capacity * 8,capacity * 8])
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain40 : state.memaddrs (table + 40)) (domain48 : state.memaddrs (table + 48))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state htabNewValuesAllocation = (some (.returned (.val (.word table))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ address : BitVec 64, address.toNat < table.toNat → post.memory address = state.memory address := by
  obtain ⟨guard,finish,restSafe⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,memory,_,heapNext,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "vals") (ofString "t") _
      (htabNewValues table keyLength capacity) (capacity * 8) table 40 htabNewUsedAllocation
      (by decide) arguments code (by omega) heap guard finish tableLocal domain40
  have nt : ofString "vals" ≠ ofString "t" := by decide
  have nc : ofString "vals" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨post,tail,empty,cost,remaining,lastCode,lastAddresses,lastEndian,frame⟩ :=
    evaluate_htabNew_used_allocation_before_header ready table keyLength capacity (postCode.trans code) (by omega)
      heapNext restSafe keyBound tableAligned budget t c
      (by rw [addresses]; exact domain48) (by rw [addresses]; exact domain56) (by rw [addresses]; exact domain64)
      (by simpa only [addresses] using wordDomain) (by simpa only [addresses] using byteDomain)
  rw [source_htabNew_values_allocation,run]
  rw [tail]
  refine ⟨_,rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 5; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
  intro address before
  rw [frame address before,memory]
  exact sourceWriteWord_before_header state table address _ 40 (by omega) (by decide) before

#print axioms evaluate_htabNew_values_allocation_before_header
end InitECandidate.Runtime

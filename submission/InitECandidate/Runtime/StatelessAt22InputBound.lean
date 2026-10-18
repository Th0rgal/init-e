import InitECandidate.Runtime.StatelessAt22
import InitECandidate.Runtime.StatelessPayloadInputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The actual initialized At22 entry inherits its input geometry and
capped aligned heap from the original prefix. No allocation reserve is
required for the complete remaining stateless decoder. -/
theorem evaluate_stateless_at22_input_bounded {F : Type}
    (state entry : PanSemStateFiniteExact 64 F) (pointer length heapPointer offsets : BitVec 64)
    (valid : FullAt22Entry state pointer length heapPointer offsets entry)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode)
    (budget : sszSplitBound length + length.toNat + 525 ≤ entry.clock) :
    let evaluated := evaluateHOLFiniteState entry (statelessAt 22)
    entry.clock ≤ evaluated.2.clock + (sszSplitBound length + length.toNat + 525) ∧
      evaluated.2.clock ≤ entry.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨p,len,installed,domain,_⟩ := fullAt22_locals state pointer length heapPointer offsets entry valid
  obtain ⟨onp,ow,opl,ovh,orq,_,wit,pl,vh,rq,nlen,long,onpEq,_,owLe,spanNat,oplEq,plLe,vhLe,rqLe⟩ :=
    fullAt22_geometry state pointer length heapPointer offsets entry valid
  obtain ⟨np,nl,atNp,atNl,npNat,innerFits⟩ := fullAt22_span state pointer length heapPointer offsets entry valid inputFits
  have nlEq : nl = ow - onp := by rw [nlen] at atNl; exact (Option.some.inj atNl).symm |> fun h => by cases h; rfl
  have lenNat : (length - 2).toNat = length.toNat - 2 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using long)]; simp
  have costLe : sszSplitBound (length - 2) + (length - 2).toNat + 525 ≤
      sszSplitBound length + length.toNat + 525 := by
    unfold sszSplitBound
    rw [lenNat]
    omega
  obtain ⟨e8,o0,o1,pre,mid⟩ := valid
  obtain ⟨_,_,_,_,preGlobals,_,_,_⟩ := pre
  obtain ⟨_,_,request,_,_,_,_,_,_,_,_,_,_,_,entryGlobals,_,_,_⟩ := mid
  have capacity : heapPointer.toNat + 96 ≤ 33806089496 := by
    have reqNat := BitVec.le_def.mp request
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact heapBound)] at reqNat
    change 96 ≤ 33806089496 - heapPointer.toNat at reqNat
    omega
  have nextNat : (allocationEnd heapPointer 96).toNat = heapPointer.toNat + 96 :=
    allocationEnd_aligned_toNat heapPointer 96 capacity aligned (by decide)
  have nextHeap : entry.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd heapPointer 96))) := by
    rw [entryGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nextOffsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [entryGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,preGlobals,atOffsets,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" by decide]
  have bound := evaluate_stateless_payload_input_bounded entry (pointer + 2) (length - 2) ow np nl opl orq ovh offsets
    (allocationEnd heapPointer 96) p len wit atNp atNl rq vh pl nextOffsets nextHeap
    (by rw [nextNat]; exact capacity) (by rw [nextNat]; omega) (by rw [nextNat]; omega)
    (by omega) (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
    (by rw [domain]; exact domain16) (by rw [domain]; exact domain24)
    (fun a lo hi => by rw [domain]; exact heapArena a (by rw [nextNat] at lo; omega) hi)
    (installed.trans code) (by rw [BitVec.le_def,lenNat]; exact owLe)
    (by rw [BitVec.le_def,oplEq]; exact plLe) (by rw [BitVec.le_def,nlEq,spanNat]; omega)
    (by rw [nlEq,spanNat,lenNat]; omega) (by omega)
  exact ⟨by have consumed := bound.1; omega,bound.2⟩

#print axioms evaluate_stateless_at22_input_bounded
end InitECandidate.Runtime

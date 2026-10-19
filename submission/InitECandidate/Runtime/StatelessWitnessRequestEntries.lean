import InitECandidate.Runtime.DecodeRequestsHashEntries
import InitECandidate.Runtime.StatelessWitnessMemFrame
import InitECandidate.Runtime.RlpSliceRecordFrame
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HtrRequestsDecoded.after_frame {F : Type} {state post : PanSemStateFiniteExact 64 F} {record : BitVec 64}
    (decoded : HtrRequestsDecoded state record) (memory : post.memory = state.memory)
    (domain : post.memaddrs = state.memaddrs) : HtrRequestsDecoded post record := by
  intro index inside
  obtain ⟨pointer,count,entry,small⟩ := decoded index inside
  exact ⟨pointer,count,entry.after_frame state post record index pointer count domain (congrFun memory _) (congrFun memory _),small⟩

/-- The actual witness decoder preserves the earlier 80-byte request table.
Scratch offsets and witness-header stores are separated by the decoder layout. -/
theorem stateless_witness_preserves_request_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (wp length si offsets heap record : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word wp)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (heapAligned : heap.toNat % 8 = 0)
    (recordBefore : record.toNat + 80 ≤ heap.toNat)
    (scratchBefore : offsets.toNat + 24 ≤ record.toNat) (siBefore : si.toNat + 88 ≤ record.toNat)
    (decoded : HtrRequestsDecoded state record)
    (run : evaluateHOLFiniteState state (statelessAt 32) = (some (.returned value),post)) :
    HtrRequestsDecoded post record := by
  have metadata := evaluateHOLFiniteState_metadata state (statelessAt 32)
  rw [run] at metadata
  intro index inside
  obtain ⟨pointer,count,entry,small⟩ := decoded index inside
  refine ⟨pointer,count,?_,small⟩
  apply entry.after_record_frame state post record index pointer count inside (by omega) metadata.2.1
  intro watched lo hi
  have separate (base : BitVec 64) (offset span : Nat)
      (before : base.toNat + span ≤ record.toNat) (inSpan : offset < span) :
      watched ≠ base + BitVec.ofNat 64 offset := by
    apply word_ne_of_toNat
    rw [word_add_toNat base offset (by have := record.isLt; omega)]
    omega
  exact stateless_witness_returned_memory state post wp length si offsets heap watched value code atPointer atLength atSi
    atOffsets atHeap heapBound heapAligned (by omega)
    ⟨by simpa using separate offsets 0 24 scratchBefore (by decide),separate offsets 8 24 scratchBefore (by decide),
      separate offsets 16 24 scratchBefore (by decide)⟩
    ⟨separate si 40 88 siBefore (by decide),separate si 48 88 siBefore (by decide),separate si 56 88 siBefore (by decide),
      separate si 64 88 siBefore (by decide),separate si 72 88 siBefore (by decide),separate si 80 88 siBefore (by decide)⟩ run

#print axioms HtrRequestsDecoded.after_frame
#print axioms stateless_witness_preserves_request_entries
end InitECandidate.Runtime

import InitECandidate.Runtime.DecodeHeaderTableMemoryReach
import InitECandidate.Runtime.DecodeHeaderFieldsEntryReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem record_clock {F : Type} {s : PanSemStateFiniteExact 64 F} {prog cont : ProgHOL 64}
    {P : PanSemStateFiniteExact 64 F → Prop} {cost : Nat} (h : Reaches s prog P cost cont) :
    Reaches s prog (fun next => P next ∧ s.clock ≤ next.clock + cost) cost cont := by
  rcases h with ⟨next,facts,spent,remaining,agreement⟩ | aborted
  · exact Or.inl ⟨next,⟨facts,spent⟩,spent,remaining,agreement⟩
  · exact Or.inr aborted

/-- The actual decoder prefix through the first record store reaches the first
header field parser with an accepted count, real field table and allocated record. -/
theorem decode_header_initial_fields_memory_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit + 2 ≤ s.clock) :
    Reaches s (decodeHeaderAt 0)
      (fun ready => ∃ count flag : BitVec 64,
        count.toNat ≤ length.toNat ∧
        ((count = 21 ∧ flag = 0) ∨ (count = 23 ∧ flag = 1)) ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "n") = some (.val (.word count)) ∧
        ready.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
        ready.locals.lookup (ofString "h") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        RlpSliceInputPrefix ready array pointer length count.toNat ∧
        ready.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (allocationEnd array (count * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd array (count * 16)) 248).toNat ∧
        (allocationEnd (allocationEnd array (count * 16)) 248).toNat ≤ 33806089496 ∧
        (allocationEnd (allocationEnd array (count * 16)) 248).toNat % 8 = 0 ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → ready.memory address = s.memory address))
      ((decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit) + 2) (decodeHeaderAt 9) := by
  have first := decode_header_table_memory_reaches s pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    ceilingAligned inputAfter inputBeforeArray (by omega)
  apply reaches_trans s (decodeHeaderAt 0) (decodeHeaderAt 5) (decodeHeaderAt 9) _ _
    (decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit) 2 (record_clock first)
  intro parsed facts
  obtain ⟨⟨count,countBound,arr,n,table,heapBinding,scratchBinding,frameBinding,domain,installed,extent,cap,al,oldMemory⟩,spent⟩ := facts
  have fields := decode_header_fields_entry_reaches parsed array count pointer length (allocationEnd array (count * 16))
    (installed.trans code) arr n heapBinding table extent cap (by omega)
  apply reaches_mono parsed (decodeHeaderAt 5) (decodeHeaderAt 9) _ _ 2 2 (le_refl _) ?_ fields
  intro ready facts
  obtain ⟨flag,accepted,arrReady,nReady,flagReady,hReady,tableReady,domainReady,codeReady,heapReady,other,recordExtent,recordCap,recordAligned,memory⟩ := facts
  refine ⟨count,flag,countBound,accepted,arrReady,nReady,flagReady,hReady,tableReady,heapReady,?_,?_,
    domainReady.trans domain,codeReady.trans installed,recordExtent,recordCap,recordAligned,?_⟩
  · rw [other (ofString "scratch_ptr") (by decide)]; exact scratchBinding
  · rw [other (ofString "frame_mem_ptr") (by decide)]; exact frameBinding

  · intro address lo hi
    exact (memory address (by omega)).trans (oldMemory address lo hi)

#print axioms decode_header_initial_fields_memory_reaches
end InitECandidate.Runtime

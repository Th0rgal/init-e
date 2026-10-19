import InitECandidate.Runtime.DecodeHeaderSliceSetupReach
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

/-- The actual initial full RLP parse, list-kind guard, slice constructor and
array/count bindings reach the header count guard with a real readable table. -/
theorem decode_header_table_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 0)
      (fun ready => ∃ count : BitVec 64,
        count.toNat ≤ length.toNat ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "n") = some (.val (.word count)) ∧
        RlpSliceInputPrefix ready array pointer length count.toNat ∧
        ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
        (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧ (allocationEnd array (count * 16)).toNat % 8 = 0)
      (decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit) (decodeHeaderAt 5) := by
  have first := decode_header_list_entry_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  apply reaches_trans s (decodeHeaderAt 0) (decodeHeaderAt 2) (decodeHeaderAt 5) _ _
    (decodeHeaderRlpCost inputLimit) (decodeHeaderSlicesCost inputLimit) (record_clock first)
  intro parsed facts
  obtain ⟨⟨input,size,sizeBound,positive,starts,ends,fits,locals,domain,installed,globals,memory⟩,spent⟩ := facts
  have atTop : parsed.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word (1#64)),.val (.word input),.val (.word size),.val (.word length)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have slices := decode_header_slice_setup_reaches parsed input size length scratch frame array pointer length ceiling inputLimit
    atTop fits (by omega) limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (installed.trans code) orderedFrame framePositive scratchBelow (by intro address lo hi; rw [domain]; exact arena address lo hi)
    (by rw [globals]; exact heap) arrayBound countLimit
    (by intro address lo hi; rw [domain]; exact heapArena address lo hi)
    (Or.inr ⟨ceilingAligned,by omega⟩) (by omega) starts ends (by omega)
  apply reaches_mono parsed (decodeHeaderAt 2) (decodeHeaderAt 5) _ _
    (decodeHeaderSlicesCost inputLimit) (decodeHeaderSlicesCost inputLimit) (le_refl _) ?_ slices
  intro ready facts
  obtain ⟨count,countBound,readyLocals,table,heapBinding,scratchBinding,frameBinding,readyDomain,readyCode,extent,cap,al⟩ := facts
  refine ⟨count,countBound,?_,?_,table,heapBinding,scratchBinding,frameBinding,readyDomain.trans domain,readyCode.trans installed,extent,cap,al⟩
  · rw [readyLocals]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [readyLocals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms decode_header_table_entry_reaches
end InitECandidate.Runtime

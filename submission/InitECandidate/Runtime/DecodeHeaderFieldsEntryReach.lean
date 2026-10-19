import InitECandidate.Runtime.DecodeHeaderAllocationReach
import InitECandidate.Runtime.DecodeHeaderFlagStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real count check, record allocation and first store reach the first
field parser with the original readable slice table, within two source ticks. -/
theorem decode_header_fields_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (capped : heap.toNat ≤ 33806089496) (budget : 2 ≤ s.clock) :
    Reaches s (decodeHeaderAt 5)
      (fun post => ∃ flag : BitVec 64,
        ((count = 21 ∧ flag = 0) ∨ (count = 23 ∧ flag = 1)) ∧
        post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word count)) ∧
        post.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
        post.locals.lookup (ofString "h") = some (.val (.word heap)) ∧
        RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 248))) ∧
        (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
        heap.toNat + 248 ≤ (allocationEnd heap 248).toNat ∧
        (allocationEnd heap 248).toNat ≤ 33806089496 ∧ (allocationEnd heap 248).toNat % 8 = 0 ∧
        (∀ address : BitVec 64, address.toNat < heap.toNat → post.memory address = s.memory address))
      2 (decodeHeaderAt 9) := by
  apply reaches_trans s (decodeHeaderAt 5) (decodeHeaderAt 8) (decodeHeaderAt 9) _ _ 2 0
    (decode_header_allocation_reaches s array count heap code atArray atCount atHeap capped budget)
  intro allocated facts
  obtain ⟨flag,kind,arr,n,flagLocal,header,memory,domain,installed,heapBinding,other,extent,cap,al⟩ := facts
  have tableReady : RlpSliceInputPrefix allocated array input inputLength count.toNat :=
    table.after_memory_below s allocated array count input inputLength heap before domain (fun address _ => congrFun memory address)
  have store := decode_header_flag_store_reaches allocated array count input inputLength heap flag (installed.trans code)
    header flagLocal tableReady before
  apply reaches_mono allocated (decodeHeaderAt 8) (decodeHeaderAt 9) _ _ 0 0 (le_refl _) ?_ store
  intro post kept
  obtain ⟨postTable,locals,globals,postDomain,postCode,postMemory⟩ := kept
  refine ⟨flag,kind,?_,?_,?_,?_,postTable,postDomain.trans domain,postCode.trans installed,?_,?_,extent,cap,al,?_⟩
  · rw [locals]; exact arr
  · rw [locals]; exact n
  · rw [locals]; exact flagLocal
  · rw [locals]; exact header
  · rw [globals]; exact heapBinding
  · intro name different
    rw [globals]; exact other name different
  · intro address below
    rw [postMemory address below,memory]

#print axioms decode_header_fields_entry_reaches
end InitECandidate.Runtime

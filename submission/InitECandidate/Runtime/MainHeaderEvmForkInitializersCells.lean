import InitECandidate.Runtime.MainHeaderEvmForkInitializers
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.MainHeaderInitReachCells
import InitECandidate.Runtime.MainEvmForkInitializersCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_main_header_evm_fork_initializers_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroHeader : state.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (forkWords : ∀ entry ∈ forkInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 816 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 985 ≤ state.clock) :
    Reaches state (mainAt 11) (HeaderEvmForkInitializerContinuation state pointer) 985 (mainAt 14) := by
  have reached := evaluate_main_headerInit_reaches_cells state pointer code heap zeroHeader aligned (by omega)
    (by intro address cellAligned lower upper; exact arena address cellAligned (by omega) upper) (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · obtain ⟨middleGlobals,middleLocals,middleCode,middleDomain,middleHeap⟩ := valid
    have addNat : (pointer + 8).toNat = pointer.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change pointer.toNat + 8 < 2^64; omega)]
      rfl
    have endEq : allocationEnd pointer 8 = pointer + 8 := by
      apply BitVec.eq_of_toNat_eq
      rw [allocationEnd_aligned_toNat pointer 8 (by change pointer.toNat + 8 ≤ 33806089496; omega) aligned (by decide),addNat]
      rfl
    have heapAt : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (pointer + 8))) := by
      rw [endEq] at middleHeap
      exact middleHeap
    have kept (key : MlS) (notHeap : key ≠ ofString "heap_ptr") (notHeader : key ≠ ofString "hdr_zero8") :
        middle.globals.lookup key = state.globals.lookup key := by
      rw [middleGlobals,headerInitGlobals_lookup_other _ _ _ notHeap notHeader]
    have forkDistinct : ∀ entry ∈ forkInitAllocations,
        entry.1 ≠ ofString "heap_ptr" ∧ entry.1 ≠ ofString "hdr_zero8" := by decide
    have middleForkWords : ∀ entry ∈ forkInitAllocations, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      obtain ⟨word,binding⟩ := forkWords entry member
      obtain ⟨notHeap,notHeader⟩ := forkDistinct entry member
      exact ⟨word,(kept entry.1 notHeap notHeader).trans binding⟩
    have nextRun := evaluate_main_evm_fork_initializers_cells middle (pointer + 8)
      oldTopic oldSystem oldNull oldEmpty oldKey oldHeader (middleCode.trans code) heapAt
      ((kept _ (by decide) (by decide)).trans topicSlot)
      ((kept _ (by decide) (by decide)).trans systemSlot)
      ((kept _ (by decide) (by decide)).trans nullSlot)
      ((kept _ (by decide) (by decide)).trans emptySlot)
      ((kept _ (by decide) (by decide)).trans keySlot)
      ((kept _ (by decide) (by decide)).trans headerSlot) middleForkWords
      ((kept _ (by decide) (by decide)).trans stateGlobal)
      ((kept _ (by decide) (by decide)).trans padGlobal)
      (by rw [addNat]; omega) (by rw [addNat]; omega) (by rw [addNat]; omega)
      (by intro address cellAligned lower upper; rw [middleDomain]; exact arena address cellAligned lower upper) (by omega)
    have adapted : Reaches middle (mainAt 12) (HeaderEvmForkInitializerContinuation state pointer) 974 (mainAt 14) :=
      reaches_mono middle (mainAt 12) (mainAt 14) (EvmForkInitializerContinuation middle (pointer + 8))
        (HeaderEvmForkInitializerContinuation state pointer) 974 974 (by omega)
        (by
          intro next normal
          obtain ⟨globals,locals,installed,domain,finalHeap,heapEnd,heapNat⟩ := normal
          refine ⟨?_,locals.trans middleLocals,installed.trans middleCode,domain.trans middleDomain,
            finalHeap,heapEnd,?_⟩
          · rw [globals,middleGlobals]
            rfl
          · rw [addNat] at heapNat
            omega)
        nextRun
    exact reaches_trans state (mainAt 11) (mainAt 12) (mainAt 14)
      (fun next => next = middle) (HeaderEvmForkInitializerContinuation state pointer) 11 974
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 11 985 (by omega) aborted)

#print axioms evaluate_main_header_evm_fork_initializers_cells
end InitECandidate.Runtime

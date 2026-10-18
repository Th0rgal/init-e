import InitECandidate.Runtime.MainEvmInitReach
import InitECandidate.Runtime.MainForkInitReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def evmForkInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  globalAllocationGlobals (globalAllocationGlobals globals pointer evmInitAllocations)
    (pointer + 216) forkInitAllocations

def EvmForkInitializerContinuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = evmForkInitializerGlobals state.globals pointer ∧ next.locals = state.locals ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    ∃ finalHeap : BitVec 64, next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat = pointer.toNat + 808

/-- The last two initialization calls of actual main reach input loading
within 974 source ticks or terminate early. Normal continuation has their
composed global map and an exactly 808-byte heap advance. -/
theorem evaluate_main_evm_fork_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
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
    (small : pointer.toNat + 808 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 974 ≤ state.clock) :
    Reaches state (mainAt 12) (EvmForkInitializerContinuation state pointer) 974 (mainAt 14) := by
  have reached := evaluate_main_evmInit_reaches state pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader
    code heap topicSlot systemSlot nullSlot emptySlot keySlot headerSlot stateGlobal padGlobal aligned above
    (by omega) arena (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · obtain ⟨middleGlobals,middleLocals,middleCode,middleDomain,middlePointer,middleHeap,middleNat⟩ := valid
    have addNat : (pointer + 216).toNat = pointer.toNat + 216 := by
      rw [BitVec.toNat_add_of_lt (by change pointer.toNat + 216 < 2^64; omega)]
      rfl
    have middlePointerEq : middlePointer = pointer + 216 := by
      apply BitVec.eq_of_toNat_eq
      rw [middleNat,addNat]
    have heapAt : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (pointer + 216))) := by
      rw [middlePointerEq] at middleHeap
      exact middleHeap
    have disjoint : ∀ entry ∈ forkInitAllocations, entry.1 ≠ ofString "heap_ptr" ∧
        (∀ other ∈ evmInitAllocations, entry.1 ≠ other.1) := by decide
    have middleWords : ∀ entry ∈ forkInitAllocations, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      obtain ⟨word,binding⟩ := forkWords entry member
      obtain ⟨notHeap,notEvm⟩ := disjoint entry member
      refine ⟨word,?_⟩
      rw [middleGlobals,globalAllocationGlobals_lookup_other _ _ _ _ notHeap notEvm]
      exact binding
    obtain ⟨oldZero,zeroSlot⟩ := middleWords (ofString "zero32",32) (by simp [forkInitAllocations])
    obtain ⟨oldPrecompile,precompileSlot⟩ := middleWords (ofString "precompile_addrs",360) (by simp [forkInitAllocations])
    have nextRun := evaluate_main_forkInit_reaches middle (pointer + 216) oldZero oldPrecompile
      (middleCode.trans code) heapAt zeroSlot precompileSlot
      (by intro entry member; exact middleWords entry (by simp [forkInitAllocations,member]))
      (by rw [addNat]; omega) (by rw [addNat]; omega)
      (by
        intro address lower upper
        rw [middleDomain]
        apply arena address
        · rw [addNat] at lower; omega
        · rw [addNat] at upper; omega)
      (by omega)
    have adapted : Reaches middle (mainAt 13) (EvmForkInitializerContinuation state pointer) 516 (mainAt 14) :=
      reaches_mono middle (mainAt 13) (mainAt 14) (ForkInitContinuation middle (pointer + 216))
        (EvmForkInitializerContinuation state pointer) 516 516 (by omega)
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
    exact reaches_trans state (mainAt 12) (mainAt 13) (mainAt 14)
      (fun next => next = middle) (EvmForkInitializerContinuation state pointer) 458 516
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 458 974 (by omega) aborted)

#print axioms evaluate_main_evm_fork_initializers
end InitECandidate.Runtime

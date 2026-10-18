import InitECandidate.Runtime.LateInitializerGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def lastFiveInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) : HolFiniteMapExact MlS (ValueHOL 64) :=
  headerEvmForkInitializerGlobals (ripemdBlakeInitializerGlobals globals) 2713730616

def LastFiveInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = lastFiveInitializerGlobals state.globals ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713731432))

/-- The remaining five actual initialization calls reach input loading
within 1001 source ticks or terminate earlier, with their exact composed
normal globals and heap frontier. -/
theorem evaluate_main_last_five_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752)))
    (zeroRmd : state.globals.lookup (ofString "rmd_tab") = some (.val (.word 0)))
    (rmdWords : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (zeroBlake : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (blakeWords : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
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
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 1001 ≤ state.clock) :
    Reaches state (mainAt 9) (LastFiveInitializerContinuation state) 1001 (mainAt 14) := by
  have reached := evaluate_main_ripemd_blake_initializers state code heap zeroRmd rmdWords zeroBlake blakeWords (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · obtain ⟨middleGlobals,middleCode,middleDomain,middleLocals,middleHeap⟩ := valid
    have kept (key : MlS) (member : key ∈ lateInitializerNames) :
        middle.globals.lookup key = state.globals.lookup key := by
      rw [middleGlobals,ripemdBlakeInitializerGlobals_late_lookup _ key member]
    have middleForkWords : ∀ entry ∈ forkInitAllocations, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      obtain ⟨word,binding⟩ := forkWords entry member
      have inFork : entry.1 ∈ forkInitAllocations.map Prod.fst := List.mem_map.mpr ⟨entry,member,rfl⟩
      exact ⟨word,(kept entry.1 (by simp [lateInitializerNames,inFork])).trans binding⟩
    have nextRun := evaluate_main_header_evm_fork_initializers middle 2713730616
      oldTopic oldSystem oldNull oldEmpty oldKey oldHeader (middleCode.trans code) middleHeap
      ((kept _ (by decide)).trans zeroHeader) ((kept _ (by decide)).trans topicSlot)
      ((kept _ (by decide)).trans systemSlot) ((kept _ (by decide)).trans nullSlot)
      ((kept _ (by decide)).trans emptySlot) ((kept _ (by decide)).trans keySlot)
      ((kept _ (by decide)).trans headerSlot) middleForkWords
      ((kept _ (by decide)).trans stateGlobal) ((kept _ (by decide)).trans padGlobal)
      (by decide) (by decide) (by decide)
      (by intro address lower upper; rw [middleDomain]; exact arena address lower upper) (by omega)
    have adapted : Reaches middle (mainAt 11) (LastFiveInitializerContinuation state) 985 (mainAt 14) :=
      reaches_mono middle (mainAt 11) (mainAt 14) (HeaderEvmForkInitializerContinuation middle 2713730616)
        (LastFiveInitializerContinuation state) 985 985 (by omega)
        (by
          intro next normal
          obtain ⟨globals,locals,installed,domain,finalHeap,heapEnd,heapNat⟩ := normal
          have heapEq : finalHeap = 2713731432 := by
            apply BitVec.eq_of_toNat_eq
            simpa using heapNat
          refine ⟨?_,installed.trans middleCode,domain.trans middleDomain,locals.trans middleLocals,?_⟩
          · rw [globals,middleGlobals]
            rfl
          · simpa only [heapEq] using heapEnd)
        nextRun
    exact reaches_trans state (mainAt 9) (mainAt 11) (mainAt 14)
      (fun next => next = middle) (LastFiveInitializerContinuation state) 16 985
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 16 1001 (by omega) aborted)

#print axioms evaluate_main_last_five_initializers
end InitECandidate.Runtime

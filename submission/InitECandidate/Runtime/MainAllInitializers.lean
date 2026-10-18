import InitECandidate.Runtime.FirstNineLateGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) : HolFiniteMapExact MlS (ValueHOL 64) :=
  lastFiveInitializerGlobals (firstNineInitializerGlobals globals)

def AllInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = allInitializerGlobals state.globals ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713731432))

/-- All fourteen initialization calls of the original main reach input
loading within 1893 source ticks or terminate earlier. The normal continuation
has the exact composed globals and the execution-linked final heap frontier. -/
theorem evaluate_main_all_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (hashWords : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (sszWords : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (mptWords : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (zeroHashes : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (zeroWorkspace : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0)))
    (zeroSecp : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (bnWords : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (blsWords : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64,
      state.globals.lookup name = some (.val (.word word)))
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
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 1893 ≤ state.clock) :
    Reaches state (mainAt 0) (AllInitializerContinuation state) 1893 (mainAt 14) := by
  have reached := evaluate_main_first_nine_initializers state oldHeap oldScratch oldFrame heap scratch frame
    hashWords sszWords mptWords zeroHashes zeroWorkspace zeroSecp gammaZero paramsZero bnWords b2Word expwWord
    discountZero constsZero fpZero fp2Zero g1Zero blsWords arena code (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · have kept (key : MlS) (member : key ∈ remainingInitializerNames) :
        middle.globals.lookup key = state.globals.lookup key := by
      rw [valid.1,firstNineInitializerGlobals_remaining_lookup _ key member]
    have middleRmdWords : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      obtain ⟨word,binding⟩ := rmdWords entry member
      have inRmd : entry.1 ∈ ripemdInitAllocations.map Prod.fst := List.mem_map.mpr ⟨entry,member,rfl⟩
      exact ⟨word,(kept entry.1 (by simp [remainingInitializerNames,inRmd])).trans binding⟩
    have middleBlakeWords : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
        ∃ word : BitVec 64, middle.globals.lookup name = some (.val (.word word)) := by
      intro name member
      obtain ⟨word,binding⟩ := blakeWords name member
      have inBlake : name ∈ blakeInitializerNames := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> simp [blakeInitializerNames]
      exact ⟨word,(kept name (by simp [remainingInitializerNames,inBlake])).trans binding⟩
    have middleForkWords : ∀ entry ∈ forkInitAllocations, ∃ word : BitVec 64,
        middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      obtain ⟨word,binding⟩ := forkWords entry member
      have inFork : entry.1 ∈ forkInitAllocations.map Prod.fst := List.mem_map.mpr ⟨entry,member,rfl⟩
      exact ⟨word,(kept entry.1 (by simp [remainingInitializerNames,inFork])).trans binding⟩
    have stateGlobal : middle.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)) := by
      rw [valid.1]
      exact (firstNineInitializerGlobals_keccak state.globals).1
    have padGlobal : middle.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
      rw [valid.1]
      exact (firstNineInitializerGlobals_keccak state.globals).2
    have nextRun := evaluate_main_last_five_initializers middle oldTopic oldSystem oldNull oldEmpty oldKey oldHeader
      (valid.2.1.trans code) valid.2.2.2.2 ((kept _ (by decide)).trans zeroRmd) middleRmdWords
      ((kept _ (by decide)).trans zeroBlake) middleBlakeWords ((kept _ (by decide)).trans zeroHeader)
      ((kept _ (by decide)).trans topicSlot) ((kept _ (by decide)).trans systemSlot)
      ((kept _ (by decide)).trans nullSlot) ((kept _ (by decide)).trans emptySlot)
      ((kept _ (by decide)).trans keySlot) ((kept _ (by decide)).trans headerSlot)
      middleForkWords stateGlobal padGlobal
      (by intro address lower upper; rw [valid.2.2.1]; exact arena address lower upper) (by omega)
    have adapted : Reaches middle (mainAt 9) (AllInitializerContinuation state) 1001 (mainAt 14) :=
      reaches_mono middle (mainAt 9) (mainAt 14) (LastFiveInitializerContinuation middle)
        (AllInitializerContinuation state) 1001 1001 (by omega)
        (by
          intro next normal
          refine ⟨?_,normal.2.1.trans valid.2.1,normal.2.2.1.trans valid.2.2.1,
            normal.2.2.2.1.trans valid.2.2.2.1,normal.2.2.2.2⟩
          rw [normal.1,valid.1]
          rfl)
        nextRun
    exact reaches_trans state (mainAt 0) (mainAt 9) (mainAt 14)
      (fun next => next = middle) (AllInitializerContinuation state) 892 1001
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 892 1893 (by omega) aborted)

#print axioms evaluate_main_all_initializers
end InitECandidate.Runtime

import InitECandidate.Runtime.MainFirstEightInitializers
import InitECandidate.Runtime.MainFirstSevenInitializersCells
import InitECandidate.Runtime.MainBn254InitReachCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem evaluate_main_first_eight_initializers_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
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
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 778 ≤ state.clock) :
    Reaches state (mainAt 0) (FirstEightInitializerContinuation state) 778 (mainAt 8) := by
  have reached := evaluate_main_first_seven_initializers_cells state oldHeap oldScratch oldFrame heap scratch frame
    hashWords sszWords mptWords zeroHashes zeroWorkspace zeroSecp arena code (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · have kept (name : MlS) (member : name ∈ bn254InitNames) : middle.globals.lookup name = state.globals.lookup name := by
      rw [valid.1,firstSevenInitializerGlobals_bn254_lookup _ name member]
    have middleGamma : middle.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)) := by
      rw [kept _ (by simp [bn254InitNames])]; exact gammaZero
    have middleParams : middle.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)) := by
      rw [kept _ (by simp [bn254InitNames,bn254AccelNames])]; exact paramsZero
    have middleWords : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, middle.globals.lookup name = some (.val (.word word)) := by
      intro name member
      obtain ⟨word,binding⟩ := bnWords name member
      exact ⟨word,(kept name (by simp [bn254InitNames,member])).trans binding⟩
    have middleB2 : ∃ word : BitVec 64, middle.globals.lookup (ofString "bn_b2") = some (.val (.word word)) := by
      obtain ⟨word,binding⟩ := b2Word
      exact ⟨word,(kept _ (by simp [bn254InitNames])).trans binding⟩
    have middleExpw : ∃ word : BitVec 64, middle.globals.lookup (ofString "bn_expw") = some (.val (.word word)) := by
      obtain ⟨word,binding⟩ := expwWord
      exact ⟨word,(kept _ (by simp [bn254InitNames])).trans binding⟩
    have nextRun := evaluate_main_bn254Init_reaches_cells middle (valid.2.1.trans code) valid.2.2.2.2
      middleGamma middleParams middleWords middleB2 middleExpw
      (by intro address aligned lower upper; rw [valid.2.2.1]; apply arena address aligned <;> omega) (by omega)
    have adapted : Reaches middle (mainAt 7) (FirstEightInitializerContinuation state) 35 (mainAt 8) :=
      reaches_mono middle (mainAt 7) (mainAt 8) (Bn254InitContinuation middle)
        (FirstEightInitializerContinuation state) 35 35 (by omega)
        (by
          intro next normal
          refine ⟨?_,normal.2.1.trans valid.2.1,normal.2.2.1.trans valid.2.2.1,
            normal.2.2.2.1.trans valid.2.2.2.1,normal.2.2.2.2⟩
          rw [normal.1,valid.1]
          rfl)
        nextRun
    exact reaches_trans state (mainAt 0) (mainAt 7) (mainAt 8)
      (fun next => next = middle) (FirstEightInitializerContinuation state) 743 35
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 743 778 (by omega) aborted)

#print axioms evaluate_main_first_eight_initializers_cells
end InitECandidate.Runtime

import InitECandidate.Runtime.FirstEightBlsGlobals
import InitECandidate.Runtime.MainBlsInitReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def firstNineInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) : HolFiniteMapExact MlS (ValueHOL 64) :=
  blsInitGlobals (firstEightInitializerGlobals globals) 2713719944

def FirstNineInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = firstNineInitializerGlobals state.globals ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752))

/-- Actual main reaches RIPEMD initialization within 892 source ticks, or
terminates in an earlier initializer. Normal globals and heap are exact. -/
theorem evaluate_main_first_nine_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (blsWords : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64,
      state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 892 ≤ state.clock) :
    Reaches state (mainAt 0) (FirstNineInitializerContinuation state) 892 (mainAt 9) := by
  have reached := evaluate_main_first_eight_initializers state oldHeap oldScratch oldFrame heap scratch frame
    hashWords sszWords mptWords zeroHashes zeroWorkspace zeroSecp gammaZero paramsZero bnWords b2Word expwWord
    arena code (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · have kept (name : MlS) (member : name ∈ blsInitializerNames) : middle.globals.lookup name = state.globals.lookup name := by
      rw [valid.1,firstEightInitializerGlobals_bls_lookup _ name member]
    have middleWords : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64,
        middle.globals.lookup name = some (.val (.word word)) := by
      intro name member
      obtain ⟨word,binding⟩ := blsWords name member
      exact ⟨word,(kept name (by simp [blsInitializerNames,member])).trans binding⟩
    have nextRun := evaluate_main_blsInit_reaches middle (valid.2.1.trans code) valid.2.2.2.2
      ((kept _ (by simp [blsInitializerNames])).trans discountZero)
      ((kept _ (by simp [blsInitializerNames])).trans constsZero)
      ((kept _ (by simp [blsInitializerNames])).trans fpZero)
      ((kept _ (by simp [blsInitializerNames])).trans fp2Zero)
      ((kept _ (by simp [blsInitializerNames])).trans g1Zero) middleWords
      (by intro address lower upper; rw [valid.2.2.1]; apply arena address <;> omega) (by omega)
    have adapted : Reaches middle (mainAt 8) (FirstNineInitializerContinuation state) 114 (mainAt 9) :=
      reaches_mono middle (mainAt 8) (mainAt 9) (BlsInitContinuation middle)
        (FirstNineInitializerContinuation state) 114 114 (by omega)
        (by
          intro next normal
          refine ⟨?_,normal.2.1.trans valid.2.1,normal.2.2.1.trans valid.2.2.1,
            normal.2.2.2.1.trans valid.2.2.2.1,normal.2.2.2.2⟩
          rw [normal.1,valid.1]
          rfl)
        nextRun
    exact reaches_trans state (mainAt 0) (mainAt 8) (mainAt 9)
      (fun next => next = middle) (FirstNineInitializerContinuation state) 778 114
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 778 892 (by omega) aborted)

#print axioms evaluate_main_first_nine_initializers
end InitECandidate.Runtime

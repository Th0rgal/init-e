import InitECandidate.Runtime.MainRipemdInitReach
import InitECandidate.Runtime.MainBlakeInitReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def blakeInitializerNames : List MlS :=
  [ofString "b2_sigma",ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"]

def ripemdBlakeInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) : HolFiniteMapExact MlS (ValueHOL 64) :=
  blake2InitGlobals (globalAllocationGlobals globals 2713729752 ripemdInitAllocations) 2713730208

def RipemdBlakeInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = ripemdBlakeInitializerGlobals state.globals ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730616))

/-- Actual main through RIPEMD and BLAKE2 initialization reaches header
initialization within sixteen source ticks or terminates earlier. The normal
state uses the execution-linked heap left by first BLS initialization. -/
theorem evaluate_main_ripemd_blake_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752)))
    (zeroRmd : state.globals.lookup (ofString "rmd_tab") = some (.val (.word 0)))
    (rmdWords : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (zeroBlake : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (blakeWords : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (budget : 16 ≤ state.clock) :
    Reaches state (mainAt 9) (RipemdBlakeInitializerContinuation state) 16 (mainAt 11) := by
  have reached := evaluate_main_ripemdInit_reaches state 2713729752 code heap zeroRmd rmdWords
    (by decide) (by decide) (by omega)
  rcases reached with ⟨middle,valid,spent,remaining,agreement⟩ | aborted
  · obtain ⟨middleGlobals,middleLocals,middleCode,middleDomain,middlePointer,middleHeap,middleNat⟩ := valid
    have pointerEq : middlePointer = 2713730208 := by
      apply BitVec.eq_of_toNat_eq
      simpa using middleNat
    have heapAt : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730208)) := by
      rw [pointerEq] at middleHeap
      exact middleHeap
    have distinct : ∀ name ∈ blakeInitializerNames, name ≠ ofString "heap_ptr" ∧
        (∀ entry ∈ ripemdInitAllocations, name ≠ entry.1) := by decide
    have kept (name : MlS) (member : name ∈ blakeInitializerNames) :
        middle.globals.lookup name = state.globals.lookup name := by
      obtain ⟨notHeap,notRmd⟩ := distinct name member
      rw [middleGlobals,globalAllocationGlobals_lookup_other _ _ _ _ notHeap notRmd]
    have middleZero : middle.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)) :=
      (kept _ (by simp [blakeInitializerNames])).trans zeroBlake
    have middleWords : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
        ∃ word : BitVec 64, middle.globals.lookup name = some (.val (.word word)) := by
      intro name member
      obtain ⟨word,binding⟩ := blakeWords name member
      refine ⟨word,(kept name ?_).trans binding⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [blakeInitializerNames]
    have nextRun := evaluate_main_blakeInit_reaches middle (middleCode.trans code) heapAt middleZero middleWords (by omega)
    have adapted : Reaches middle (mainAt 10) (RipemdBlakeInitializerContinuation state) 7 (mainAt 11) :=
      reaches_mono middle (mainAt 10) (mainAt 11) (BlakeInitContinuation middle)
        (RipemdBlakeInitializerContinuation state) 7 7 (by omega)
        (by
          intro next normal
          refine ⟨?_,normal.2.1.trans middleCode,normal.2.2.1.trans middleDomain,
            normal.2.2.2.1.trans middleLocals,normal.2.2.2.2⟩
          rw [normal.1,middleGlobals]
          rfl)
        nextRun
    exact reaches_trans state (mainAt 9) (mainAt 10) (mainAt 11)
      (fun next => next = middle) (RipemdBlakeInitializerContinuation state) 9 7
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 9 16 (by omega) aborted)

#print axioms evaluate_main_ripemd_blake_initializers
end InitECandidate.Runtime

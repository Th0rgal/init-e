import InitECandidate.Runtime.FirstFourInitializerGlobals
import InitECandidate.Runtime.MainMptInitReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def FirstFiveInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = globalAllocationGlobals (firstFourInitializerGlobals state.globals) 2713717456 mptInitAllocations ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717640))

/-- Actual main through the fifth initializer, with both normal continuation
and early termination covered in 737 source ticks. -/
theorem evaluate_main_first_five_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (zero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 737 ≤ state.clock) :
    Reaches state (mainAt 0) (FirstFiveInitializerContinuation state) 737 (mainAt 5) := by
  obtain ⟨middle,prefixRun,clock,_,locals,installed,domain,globals,midHeap,_,_⟩ :=
    evaluate_main_first_four_initializers state oldHeap oldScratch oldFrame heap scratch frame hashWords sszWords zero
      (by intro address lower upper; apply arena address <;> omega) code (by omega)
  change middle.globals = firstFourInitializerGlobals state.globals at globals
  have keccak := firstFourInitializerGlobals_keccak state.globals
  have midWords : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      middle.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    obtain ⟨word,present⟩ := mptWords entry member
    refine ⟨word,?_⟩
    rw [globals,firstFourInitializerGlobals_mpt_workspace state.globals entry (List.mem_append_left _ member)]
    exact present
  have reached := evaluate_main_mptInit_reaches middle
    (by rw [globals]; exact keccak.1) (by rw [globals]; exact keccak.2) midHeap midWords (installed.trans code)
    (by omega) (by intro address lower upper; rw [domain]; exact arena address lower upper)
  rcases reached with ⟨next,valid,cost,remaining,agreement⟩ | abort
  · left
    obtain ⟨nextGlobals,nextCode,nextDomain,nextLocals,nextHeap⟩ := valid
    refine ⟨next,⟨?_,nextCode.trans installed,nextDomain.trans domain,nextLocals.trans locals,nextHeap⟩,
      by omega,by omega,?_⟩
    · rw [nextGlobals,globals]
    · rw [prefixRun]
      exact agreement
  · right
    obtain ⟨result,returned,noReturn,cost,remaining,noTimeout⟩ := abort
    refine ⟨result,?_,noReturn,?_,?_,?_⟩
    · rw [prefixRun]
      exact returned
    · rw [prefixRun]
      omega
    · rw [prefixRun]
      omega
    · intro _
      exact noTimeout (by omega)

#print axioms evaluate_main_first_five_initializers
end InitECandidate.Runtime

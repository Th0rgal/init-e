import InitECandidate.Runtime.StackAllocZeroCorrect
import InitECandidate.Runtime.ActualAllocationFree

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Proofs.BackendStages

/-- The actual input to allocation lowering satisfies the runtime syntax check. -/
theorem actual_compiled_allocationFree :
    allocationFreeCode (Flapjack.Compiler.Backend.StackRawCall.compile Native.stack) = true := by
  rw [Raw.compile_eq]
  exact actual_allocationFree

/-- Instantiate the code half of the runtime invariant from the kernel-checked
certificate for every actual generated Raw procedure. The oracle condition is
kept explicit until the compiler initialization bridge discharges it. -/
theorem actual_raw_freeState {C F : Type} (s : StackSemStateFiniteExact 64 C F)
    (code : s.code = sptFromAList Raw.stack)
    (oracle : ∀ n, allocationFreeCode (s.compileOracle n).2.1 = true) : FreeState s := by
  constructor
  · intro key body lookup
    rw [code, sptLookup_sptFromAList] at lookup
    exact allocationFreeCode_member _ actual_allocationFree (key, body)
      (sptAListLookup_mem _ _ _ lookup)
  · intro n key body member
    exact allocationFreeCode_member _ (oracle n) (key, body) member

/-- Actual Raw entry execution crosses allocation lowering with exactly the
same initial clock, rather than an unbounded existential fuel increase. -/
theorem actual_raw_entry_same_clock {C F : Type}
    (anything : WordSemGcFun 64) (cr : CompileFn 64 C)
    (s t : StackSemStateFiniteExact 64 C F) (entry : Nat)
    (r : Option (StackSemResult 64)) (c : DataToWord.Config)
    (regs : HolFiniteMapExact Nat (WordLocW 64))
    (code : s.code = sptFromAList Raw.stack)
    (oracle : ∀ n, allocationFreeCode (s.compileOracle n).2.1 = true)
    (run : evaluate (.call none (.inl entry) none, s) = (r, t))
    (notError : r ≠ some .error) (pre : Pre cr c s regs) :
    ∃ regs1, evaluate (.call none (.inl entry) none, Res anything cr c s regs) =
      (r, Res anything cr c t regs1) ∧ Post r t regs1 := by
  apply Zero.allocationFree_same_clock anything cr _ s t r c regs
    (by simp [allocationFree]) (actual_raw_freeState s code oracle) run notError
  · simp [StackProps.allocArg]
  · exact pre

#print axioms actual_raw_entry_same_clock
end InitECandidate.Runtime.StackAlloc

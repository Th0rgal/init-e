import InitECandidate.Runtime.ForkInitCallOutcome
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def ForkInitContinuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = globalAllocationGlobals state.globals pointer forkInitAllocations ∧
    next.locals = state.locals ∧ next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    ∃ finalHeap : BitVec 64, next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat = pointer.toNat + 592

theorem source_main_forkInit_call : mainAt 13 =
    .seq (.call (some (none,none)) (ofString "fork_init") []) (mainAt 14) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Main reaches input loading with the computed fork globals and heap, or
terminates earlier, within the all-outcome 516-tick initializer bound. -/
theorem evaluate_main_forkInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldZero oldPrecompile : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroSlot : state.globals.lookup (ofString "zero32") = some (.val (.word oldZero)))
    (precompileSlot : state.globals.lookup (ofString "precompile_addrs") = some (.val (.word oldPrecompile)))
    (words : ∀ entry ∈ forkSuffixAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 592 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 392 → state.memaddrs address)
    (budget : 516 ≤ state.clock) :
    Reaches state (mainAt 13) (ForkInitContinuation state pointer) 516 (mainAt 14) := by
  have bounded := evaluate_forkInit_call_outcome state pointer oldZero oldPrecompile
    code heap zeroSlot precompileSlot words aligned small arena budget
  rw [source_main_forkInit_call]
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fork_init") []) with
  | mk result next =>
    rw [run] at bounded
    dsimp only at bounded
    obtain ⟨spent,remaining,noTimeout,normal⟩ := bounded
    cases result with
    | none => exact Or.inl ⟨next,normal rfl,spent,remaining,rfl⟩
    | some result =>
      right
      refine ⟨result,rfl,?_,spent,remaining,?_⟩
      · intro value equal
        have consumed := evaluate_discard_call_no_return state (ofString "fork_init") [] value
        rw [run] at consumed
        exact consumed (by rw [equal])
      · intro _ equal
        exact noTimeout (by rw [equal])

#print axioms source_main_forkInit_call
#print axioms evaluate_main_forkInit_reaches
end InitECandidate.Runtime

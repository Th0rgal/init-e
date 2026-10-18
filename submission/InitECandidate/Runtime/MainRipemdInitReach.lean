import InitECandidate.Runtime.RipemdInitCallOutcome
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def RipemdInitContinuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = globalAllocationGlobals state.globals pointer ripemdInitAllocations ∧
    next.locals = state.locals ∧ next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    ∃ finalHeap : BitVec 64, next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat = pointer.toNat + 456

theorem source_main_ripemdInit_call : mainAt 9 =
    .seq (.call (some (none,none)) (ofString "ripemd160_init") []) (mainAt 10) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Main reaches BLAKE2 initialization with exact RIPEMD globals and heap,
 or terminates early, within nine source ticks. -/
theorem evaluate_main_ripemdInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "rmd_tab") = some (.val (.word 0)))
    (words : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 456 ≤ 33806089496)
    (budget : 9 ≤ state.clock) :
    Reaches state (mainAt 9) (RipemdInitContinuation state pointer) 9 (mainAt 10) := by
  have bounded := evaluate_ripemdInit_call_outcome state pointer code heap zero words aligned small budget
  rw [source_main_ripemdInit_call]
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ripemd160_init") []) with
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
        have consumed := evaluate_discard_call_no_return state (ofString "ripemd160_init") [] value
        rw [run] at consumed
        exact consumed (by rw [equal])
      · intro _ equal
        exact noTimeout (by rw [equal])

#print axioms source_main_ripemdInit_call
#print axioms evaluate_main_ripemdInit_reaches
end InitECandidate.Runtime

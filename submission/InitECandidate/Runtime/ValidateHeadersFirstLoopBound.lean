import InitECandidate.Runtime.ValidateHeadersFirstInvariantStep
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

def validateHeadersFirstIterationCost (inputLimit : Nat) : Nat :=
  headerDecoderBodyCost inputLimit + 1 + (inputLimit * 20 + 125)

/-- The concrete loop invariant supplies the real decoder/hash runtime premises. -/
theorem runBounded_validate_headers_first_invariant_body {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat)
    (valid : ValidateHeadersFirstInvariant e s rank) (code : s.code = originalRuntimeCode)
    (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0) (budget : validateHeadersFirstIterationCost e.inputLimit ≤ s.clock) :
    RunBounded s validateHeadersFirstBody (validateHeadersFirstIterationCost e.inputLimit) := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,heapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have inside := validate_headers_first_condition_enabled s index e.count w e.cap within i n condition nonzero
  obtain ⟨pointer,length,entry⟩ := table index inside
  exact runBounded_validate_headers_first_body s e.array e.count index pointer length e.input e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
    arr i entry table e.inputBound e.inputAfter inputBefore e.tableAbove tableBefore (by have := e.inputCap; omega)
    scratch frame code e.orderedFrame e.framePositive e.scratchBelow arena heapGlobal heapBound (by have := e.inputCap; omega)
    heapArena e.ceilingAligned hs hashes inside e.tableBeforeHs e.hsBufferBound e.hashBufferBound e.hashAligned e.inputCap state pad budget

/-- The actual first loop has a finite bound in every outcome and retains
the concrete invariant on normal exit. No callee runtime premise is assumed. -/
theorem validate_headers_first_loop_ranked (e : ValidateHeadersFirstEnvironment) :
    ∀ rank, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersFirstInvariant e s rank → rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ s.clock →
      RankedOutcome s validateHeadersFirstCondition (rank * (validateHeadersFirstIterationCost e.inputLimit + 1))
        (ValidateHeadersFirstInvariant e) False
        (evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody)) := by
  apply rankedWhile_run validateHeadersFirstCondition validateHeadersFirstBody (validateHeadersFirstIterationCost e.inputLimit)
    (ValidateHeadersFirstInvariant e) False
  · exact validate_headers_first_invariant_exit e
  · intro F s n w code valid condition nonzero budget
    have ticked := validate_headers_first_invariant_dec_clock e s (n + 1) valid
    have tickCondition : evalHOLFinite (decClockHOLFinite s)
        (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)) := by
      rw [evalHOLFinite_eq_toExact] at condition ⊢
      simpa [validateHeadersFirstCondition,evalHOLExact,decClockHOLFinite] using condition
    have bodyBudget : validateHeadersFirstIterationCost e.inputLimit ≤ (decClockHOLFinite s).clock := by
      change validateHeadersFirstIterationCost e.inputLimit ≤ s.clock - 1
      omega
    have bodyBound := runBounded_validate_headers_first_invariant_body e (decClockHOLFinite s) (n+1) ticked code w tickCondition nonzero bodyBudget
    have controls := validate_headers_first_body_no_loop_control (decClockHOLFinite s)
    refine ⟨bodyBound.1,bodyBound.2.1,bodyBound.2.2,?_,?_⟩
    · intro advancing
      have normal : (evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody).1 = none :=
        advancing.resolve_right controls.1
      have run : evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody =
          (none,(evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody).2) := Prod.ext normal rfl
      obtain ⟨m,smaller,invariant⟩ := validate_headers_first_invariant_step e (decClockHOLFinite s) _ (n+1) ticked code w tickCondition nonzero bodyBudget run
      exact ⟨m,by omega,invariant,(evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersFirstBody).1⟩
    · intro broken
      exact False.elim (controls.2 broken)

#print axioms runBounded_validate_headers_first_invariant_body
#print axioms validate_headers_first_loop_ranked
end InitECandidate.Runtime

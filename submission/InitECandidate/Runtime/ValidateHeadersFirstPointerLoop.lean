import InitECandidate.Runtime.ValidateHeadersFirstPointerInvariant
import InitECandidate.Runtime.ValidateHeadersFirstAlignedHeapLoopReach
/-!
The complete actual first loop under the full pointer invariant.

Root's `ValidateHeadersFirstPointerInvariant` combines the concrete runtime
invariant with the typed index, the initialized header-pointer prefix and the
frontier bound that keeps the whole pointer buffer alive, and
`validate_headers_first_pointer_invariant_step` proves that one enabled
successful iteration re-establishes it at a strictly smaller rank.

This module turns that step into the loop theorem, exactly as the aligned-heap
loop does for its lighter invariant: the actual `while` runs within
`rank * (iteration cost + 1)` ticks in every outcome (`RankedOutcome`), a
normal exit keeps the pointer invariant at rank `0`, and the real
`At 4 -> At 5` continuation is reached with the pointer invariant and unchanged
code.  No body bound is assumed: every iteration uses the existing per-body
`RunBounded` and the loop-control facts already proved for the real body.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- The actual ranked first loop retains the full pointer invariant: the
initialized header-pointer prefix, the typed index and the frontier bound are
preserved by every normal iteration while the rank strictly decreases. -/
theorem validate_headers_first_pointer_loop_ranked (e : ValidateHeadersFirstEnvironment)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat) :
    ∀ rank, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersFirstPointerInvariant e s rank →
      rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ s.clock →
      RankedOutcome s validateHeadersFirstCondition (rank * (validateHeadersFirstIterationCost e.inputLimit + 1))
        (ValidateHeadersFirstPointerInvariant e) False
        (evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody)) := by
  apply rankedWhile_run validateHeadersFirstCondition validateHeadersFirstBody
    (validateHeadersFirstIterationCost e.inputLimit) (ValidateHeadersFirstPointerInvariant e) False
  · intro F s valid w condition
    exact validate_headers_first_invariant_exit e s valid.1 w condition
  · intro F s n w code valid condition nonzero budget
    have ticked := validate_headers_first_invariant_dec_clock e s (n+1) valid.1
    obtain ⟨_,⟨prefixIndex,atPrefixIndex,initialized⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩ := valid
    have tickedPointer : ValidateHeadersFirstPointerInvariant e (decClockHOLFinite s) (n+1) :=
      ⟨ticked,⟨prefixIndex,atPrefixIndex,
          HeaderPointerPrefix.after_frame s (decClockHOLFinite s) e.hs prefixIndex.toNat initialized
            rfl (fun slot _ => rfl)⟩,
        ⟨initialHeap,initialBinding,bufferBefore⟩⟩
    have tickCondition : evalHOLFinite (decClockHOLFinite s)
        (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
        validateHeadersFirstCondition = some (.val (.word w)) := by
      rw [evalHOLFinite_eq_toExact] at condition ⊢
      simpa [validateHeadersFirstCondition,evalHOLExact,decClockHOLFinite] using condition
    have bodyBudget : validateHeadersFirstIterationCost e.inputLimit ≤ (decClockHOLFinite s).clock := by
      change validateHeadersFirstIterationCost e.inputLimit ≤ s.clock - 1
      omega
    have bounded := runBounded_validate_headers_first_invariant_body e (decClockHOLFinite s) (n+1)
      ticked code w tickCondition nonzero bodyBudget
    have controls := validate_headers_first_body_no_loop_control (decClockHOLFinite s)
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      have normal := flow.resolve_right controls.1
      have run : evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody =
          (none,(evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody).2) :=
        Prod.ext normal rfl
      obtain ⟨m,smaller,nextInvariant⟩ := validate_headers_first_pointer_invariant_step e
        (decClockHOLFinite s) _ (n+1) hsAbove bufferBeforeHashes tickedPointer code w tickCondition
        nonzero bodyBudget run
      exact ⟨m,by omega,nextInvariant,
        (evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersFirstBody).1⟩
    · intro broken
      exact (controls.2 broken).elim

/-- At rank `0` the invariant's index has reached the header count, so the
initialized pointer prefix covers the whole header-pointer buffer.  The typed
index is unique (the invariant's index and the prefix's index are the same
local), which turns the prefix at `index.toNat` into the prefix at
`e.count.toNat`. -/
theorem validate_headers_first_pointer_prefix_exhausted {F : Type}
    (e : ValidateHeadersFirstEnvironment) (s : PanSemStateFiniteExact 64 F)
    (exhausted : ValidateHeadersFirstPointerInvariant e s 0) :
    HeaderPointerPrefix s e.hs e.count.toNat := by
  obtain ⟨valid,⟨prefixIndex,atPrefixIndex,initialized⟩,_frontier⟩ := exhausted
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,
    heapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have indexEq : prefixIndex = index :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atPrefixIndex.symm.trans i)))
  subst prefixIndex
  have sameCount : index.toNat = e.count.toNat := by omega
  rw [← sameCount]
  exact initialized

/-- The real normal loop exit preserves the full pointer invariant at rank
`0` together with unchanged code. -/
theorem validate_headers_first_pointer_loop_normal {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (valid : ValidateHeadersFirstPointerInvariant e s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock)
    (normal : evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody) =
      (none,post)) :
    ValidateHeadersFirstPointerInvariant e post 0 ∧ post.code = s.code := by
  have exhausted := validate_headers_first_loop_normal e s post rank code valid.1 budget normal
  have small := Nat.mul_le_mul_right (validateHeadersFirstIterationCost e.inputLimit + 1)
    (validate_headers_first_invariant_rank_bound e s rank valid.1)
  have result := validate_headers_first_pointer_loop_ranked e hsAbove bufferBeforeHashes rank s code valid
    (le_trans small budget)
  rw [normal] at result
  obtain ⟨m,kept,_,_⟩ := result.2.2.2 rfl
  obtain ⟨_,⟨prefixIndex,atPrefixIndex,initialized⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩ := kept
  exact ⟨⟨exhausted.1,⟨prefixIndex,atPrefixIndex,initialized⟩,
    ⟨initialHeap,initialBinding,bufferBefore⟩⟩,exhausted.2⟩

/-- The exact first-loop continuation is reached with the full pointer
invariant, or evaluation terminates within the existing uniform budget. -/
theorem validate_headers_first_pointer_loop_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (valid : ValidateHeadersFirstPointerInvariant e s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 4)
      (fun post => ValidateHeadersFirstPointerInvariant e post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  rw [source_validate_headers_first_loop]
  apply runBounded_seq_reaches s _ _ _ _ (runBounded_validate_headers_first_loop e s rank code valid.1 budget)
  · intro value
    apply evaluate_noDirectReturnWhile
    change noDirectReturnWhile validateHeadersFirstBody = true
    rw [source_validate_headers_first_decode]
    change noDirectReturnWhile validateHeadersFirstTail = true
    rw [source_validate_headers_first_tail]
    rfl
  · intro post normal
    exact validate_headers_first_pointer_loop_normal e s post rank code hsAbove bufferBeforeHashes valid
      budget normal

#print axioms validate_headers_first_pointer_prefix_exhausted
#print axioms validate_headers_first_pointer_loop_ranked
#print axioms validate_headers_first_pointer_loop_normal
#print axioms validate_headers_first_pointer_loop_reaches
end InitECandidate.Runtime

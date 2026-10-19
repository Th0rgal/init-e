import InitECandidate.Runtime.ValidateHeadersFirstPointerIndexReach
import InitECandidate.Runtime.ValidateHeadersFirstPointerLoop
/-!
The complete pointer phase of the real first loop: `At 3 -> At 4 -> At 5`.

Root's `validate_headers_first_pointer_index_reaches` performs the actual index
initialization `i = 0` and reaches `At 4` with an empty initialized pointer
prefix at rank `e.count.toNat`; this module feeds that state straight into the
checked ranked pointer loop, so the real first loop reaches the second phase
with the complete pointer invariant at rank `0` within the unchanged uniform
budget `validateHeadersFirstLoopCost e.inputLimit`.

The only inputs are the ready allocation environment, the pointer-buffer
frontier supplied by the two real allocations, and the static geometry
`e.ceiling <= e.hs.toNat` and `e.hs.toNat + e.count.toNat * 8 <= e.hashes.toNat`.
Root modules are not modified.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- The actual index initialization plus the whole real first loop reach the
second phase with the exhausted full pointer invariant, or evaluation
terminates within the existing uniform budget. -/
theorem validate_headers_first_pointer_phase_reaches {F : Type}
    (e : ValidateHeadersFirstEnvironment) (s : PanSemStateFiniteExact 64 F)
    (ready : ValidateHeadersFirstReady e s) (code : s.code = originalRuntimeCode)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (bufferFrontier : ∃ heap : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      e.hs.toNat + e.count.toNat * 8 ≤ heap.toNat)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersFirstPointerInvariant e post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  have composed := reaches_trans_budget s (validateHeadersAt 3) (validateHeadersAt 4) (validateHeadersAt 5)
    (fun post => ValidateHeadersFirstPointerInvariant e post e.count.toNat ∧ post.code = s.code)
    (fun post => ValidateHeadersFirstPointerInvariant e post 0 ∧ post.code = s.code)
    0 (validateHeadersFirstLoopCost e.inputLimit) (by omega)
    (validate_headers_first_pointer_index_reaches e s ready bufferFrontier)
    (fun ready4 facts remaining =>
      reaches_mono ready4 (validateHeadersAt 4) (validateHeadersAt 5) _ _ _ _ (le_refl _)
        (fun post kept => ⟨kept.1,kept.2.trans facts.2⟩)
        (validate_headers_first_pointer_loop_reaches e ready4 e.count.toNat
          (facts.2.trans code) hsAbove bufferBeforeHashes facts.1 remaining))
  simpa only [Nat.zero_add] using composed

#print axioms validate_headers_first_pointer_phase_reaches
end InitECandidate.Runtime

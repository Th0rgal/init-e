import InitECandidate.Runtime.ValidateHeadersFirstHeapLoopReach
import InitECandidate.Runtime.ValidateHeadersFirstIndexReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual index declaration leaves heap globals untouched, retaining
an allocation-derived lower bound for the first while loop. -/
theorem validate_headers_first_heap_index_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (lower : BitVec 64) (s : PanSemStateFiniteExact 64 F) (ready : ValidateHeadersFirstReady e s)
    (heapLower : ∃ heap : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧ lower.toNat ≤ heap.toNat) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersFirstHeapInvariant e lower post e.count.toNat ∧ post.code = s.code)
      0 (validateHeadersAt 4) := by
  rw [source_validate_headers_index_init]
  apply reaches_dec
  intro value initialized
  have same : value = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using initialized.symm
  subst value
  exact ⟨0,rfl,⟨validate_headers_first_index_invariant e s ready,heapLower⟩,rfl⟩

/-- Index initialization and the complete original first loop reach the
second phase with the concrete invariant and the retained heap lower bound. -/
theorem validate_headers_first_heap_phase_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (lower : BitVec 64) (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode)
    (ready : ValidateHeadersFirstReady e s)
    (heapLower : ∃ heap : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧ lower.toNat ≤ heap.toNat)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersFirstHeapInvariant e lower post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  have combined := reaches_trans_budget s (validateHeadersAt 3) (validateHeadersAt 4) (validateHeadersAt 5)
    (fun next => ValidateHeadersFirstHeapInvariant e lower next e.count.toNat ∧ next.code = s.code)
    (fun post => ValidateHeadersFirstHeapInvariant e lower post 0 ∧ post.code = s.code)
    0 (validateHeadersFirstLoopCost e.inputLimit) (by omega) (validate_headers_first_heap_index_reaches e lower s ready heapLower)
    (by
      intro next facts remaining
      have tailRun := validate_headers_first_heap_loop_reaches e lower next e.count.toNat (facts.2.trans code) facts.1 remaining
      exact reaches_mono next (validateHeadersAt 4) (validateHeadersAt 5) _ _ _ _ (le_refl _)
        (fun post kept => ⟨kept.1,kept.2.trans facts.2⟩) tailRun)
  simpa only [Nat.zero_add] using combined

#print axioms validate_headers_first_heap_index_reaches
#print axioms validate_headers_first_heap_phase_reaches
end InitECandidate.Runtime

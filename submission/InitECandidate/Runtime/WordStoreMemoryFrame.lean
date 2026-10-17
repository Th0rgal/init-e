import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A one-word store leaves distinct words unchanged, including failures. -/
theorem evaluate_wordStore_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address watched : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (wordValue : ∀ parsed, @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value = some parsed → ∃ word : BitVec 64, parsed = .val (.word word))
    (separate : watched ≠ address) :
    (evaluateHOLFiniteState state (.store destination value)).2.memory watched = state.memory watched := by
  rw [evaluateHOLFiniteState_store,addressEval]
  cases evaluated : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value with
  | none => rfl
  | some parsed =>
    obtain ⟨word,rfl⟩ := wordValue parsed evaluated
    by_cases accessible : state.memaddrs address
    · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible,separate]
    · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible]

#print axioms evaluate_wordStore_memory_frame
end InitECandidate.Runtime

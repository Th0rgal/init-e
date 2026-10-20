import InitECandidate.Runtime.SourceCostExnShape
import InitECandidate.Runtime.SourceCostEntryLocals
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! The payload of an entry result is bounded by the entry's return shape and
the declared exception shapes. -/

/-- Every exception shape is well formed and at most `n` words. -/
def ExnShapesBounded {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∀ eid shape, s.eshapes.lookup eid = some shape →
    isWfShapeExactHOL ([] : StructContextExact) shape = true ∧ sizeOfShapeHOL shape ≤ n

theorem payload_of_shape {value : ValueHOL 64} {n : Nat}
    (wf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true)
    (size : sizeOfShapeHOL (shapeOfHOLExact value) ≤ n) : (flattenHOL value).length ≤ n := by
  rw [flattenHOL_length_eq_sizeOfShapeHOL value wf]; exact size

theorem entry_payload_le {F : Type} {s post : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {r ev} (run : StatementRun s (.call none function []) r post ev) (ok : r ≠ some .error) {n : Nat}
    (returns : ∀ body callee returnShape,
      lookupCodeHOLFinite s.code.lookup function [] = some (body, callee, returnShape) →
      isWfShapeExactHOL ([] : StructContextExact) returnShape = true ∧ sizeOfShapeHOL returnShape ≤ n)
    (exceptions : ExnShapesBounded s n) : callPayloadWords r ≤ n := by
  have declared := run.exn_declared
  rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
  all_goals simp only [callPayloadWords]
  all_goals try omega
  · -- returned value: the entry call checked its shape against the return shape
    cases run with
    | @callDone _ _ _ _ _ _ _ returnShape bodyResult _ _ _ _ args lookup clock bodyRun plan =>
      have values : _ := args
      simp [evalListHOLFinite, evalListHOLExact] at values
      subst values
      obtain ⟨wf, size⟩ := returns _ _ _ lookup
      unfold callCostPlan at plan
      rcases bodyResult with _ | (_ | _ | _ | _ | w | ⟨eid', w⟩ | _)
      all_goals simp only at plan
      all_goals (try (cases plan; done))
      · split at plan
        · rename_i hshape
          cases plan
          rw [shapeEqHOL_eq_true] at hshape
          rw [← hshape] at wf size
          exact payload_of_shape wf size
        · cases plan
    | callHandler args lookup clock bodyRun plan handlerRun =>
      obtain ⟨_, _, _, h⟩ := globals_plan_handler_info plan
      cases h
  · obtain ⟨wf, size⟩ := exceptions eid _ (declared eid v rfl)
    exact payload_of_shape wf size

/-- Declaration evaluation adds exactly the declared exceptions. -/
theorem decls_eshapes_mem {F : Type} :
    ∀ (decls : List (DeclHOL 64)) (s s' : PanSemStateFiniteExact 64 F),
      @evaluateDeclsHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) decls = some s' →
      ∀ eid shape, s'.eshapes.lookup eid = some shape →
        s.eshapes.lookup eid = some shape ∨ (eid, shape) ∈ exceptionsHOL decls
  | [], s, s', h, eid, shape, found => by
    simp only [evaluateDeclsHOLFinite, Option.some.injEq] at h; subst h; exact Or.inl found
  | .name _ _ :: rest, s, s', h, eid, shape, found => by
    simp only [evaluateDeclsHOLFinite] at h
    simpa [exceptionsHOL] using decls_eshapes_mem rest s s' h eid shape found
  | .decl sh name e :: rest, s, s', h, eid, shape, found => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · split at h
      · simpa [exceptionsHOL, setGlobalHOLFinite] using decls_eshapes_mem rest _ s' h eid shape found
      · simp at h
    · simp at h
  | .function declaration :: rest, s, s', h, eid, shape, found => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · simpa [exceptionsHOL] using decls_eshapes_mem rest _ s' h eid shape found
    · simp at h
  | .exnDecl name sh :: rest, s, s', h, eid, shape, found => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · rcases decls_eshapes_mem rest _ s' h eid shape found with h1 | h1
      · simp only [HolFiniteMapExact.lookup_update, FUPDATE] at h1
        split at h1
        · rename_i heq
          simp only [beq_iff_eq] at heq
          subst heq; cases h1
          exact Or.inr (by simp [exceptionsHOL])
        · exact Or.inl h1
      · exact Or.inr (by simp [exceptionsHOL, h1])
    · simp at h

#print axioms decls_eshapes_mem
#print axioms entry_payload_le
end InitECandidate.Runtime.FineCost

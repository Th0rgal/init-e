import InitECandidate.Runtime.StackExecutionLabelScope
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Exactly the source grammar handled by the native derivation theorem.
Pre-removal stack/store/allocation/install primitives are excluded. -/
def executionSupported : HolProg 64 → Bool
  | .seq first second | .ite _ _ _ first second => executionSupported first && executionSupported second
  | .loop body => executionSupported body
  | .call none _ none => true
  | .call none _ (some _) => false
  | .call (some (rp, _, _, _)) _ handler => executionSupported rp &&
      (match handler with | none => true | some (hp, _, _) => executionSupported hp)
  | .skip | .inst _ | .locValue _ _ _ | .tick | .halt _ | .ret _ | .raise _
    | .break _ | .continue _ | .ffi _ _ _ _ _ _ | .shMemOp _ _ _ | .rawCall _ | .jumpLower _ _ _ => true
  | _ => false
termination_by p => sizeOf p

def executionAtomic : HolProg 64 → Bool
  | .skip | .inst _ | .locValue _ _ _ | .tick | .halt _ | .ret _ | .raise _
    | .break _ | .continue _ | .ffi _ _ _ _ _ _ | .shMemOp _ _ _ => true
  | _ => false

/-- All stored callees use the supported post-removal grammar. -/
def ExecutionCodeSupported (code : Spt (HolProg 64)) : Prop :=
  ∀ key p, sptLookup key code = some p → executionSupported p = true

/-- Successful result classes and installed returned/raised locations. The
terminal entry needs no extra location assumption; invalid result forms,
errors and source timeouts are explicitly excluded. -/
def ExecutionResultValid (code : Spt (HolProg 64)) : Option (StackSemResult 64) → Prop
  | none => True
  | some (.result (.loc sid lid)) | some (.exception (.loc sid lid)) => StackSem.locCheckExact code (sid, lid)
  | some (.halt (.word _)) | some (.finalFFI _) | some (.break _) | some (.continue _) => True
  | _ => False

/-- Classify an actual source result. Unsupported forms stay control exits;
ExecutionResultValid rules them out before derivation construction. -/
def executionKindOfResult : Option (StackSemResult 64) → ExecutionKind
  | none => .normal
  | some (.halt (.word value)) => .terminal (.halt (.word value))
      (if value = 0 then .success else .resourceLimitHit)
  | some (.finalFFI event) => .terminal (.finalFFI event) (.ffiOutcome event)
  | some result => .exit result

theorem executionKindOfResult_result (result : Option (StackSemResult 64)) :
    (executionKindOfResult result).result = result := by
  cases result with
  | none => rfl
  | some result =>
    cases result <;> try rfl
    rename_i value
    cases value <;> rfl

theorem ExecutionResultValid.nonerror {code : Spt (HolProg 64)} {result : Option (StackSemResult 64)}
    (valid : ExecutionResultValid code result) : result ≠ some .error := by
  intro eq
  subst result
  exact valid

theorem ExecutionResultValid.nontimeout {code : Spt (HolProg 64)} {result : Option (StackSemResult 64)}
    (valid : ExecutionResultValid code result) : result ≠ some .timeOut := by
  intro eq
  subst result
  exact valid

theorem executionSupported_seq {first second : HolProg 64} :
    executionSupported (.seq first second) = true ↔ executionSupported first = true ∧ executionSupported second = true := by
  simp only [executionSupported, Bool.and_eq_true]

theorem executionSupported_ite {first second : HolProg 64} {cmp reg operand} :
    executionSupported (.ite cmp reg operand first second) = true ↔
      executionSupported first = true ∧ executionSupported second = true := by
  simp only [executionSupported, Bool.and_eq_true]

theorem executionSupported_loop {body : HolProg 64} :
    executionSupported (.loop body) = true ↔ executionSupported body = true := by
  rw [executionSupported]

theorem executionSupported_return {rp : HolProg 64} {link l1 l2 dest handler}
    (supported : executionSupported (.call (some (rp, link, l1, l2)) dest handler) = true) :
    executionSupported rp = true := by
  cases handler with
  | none => simpa [executionSupported] using supported
  | some packet =>
    rcases packet with ⟨hp, hs, hl⟩
    simp only [executionSupported, Bool.and_eq_true] at supported
    exact supported.1

theorem executionSupported_handler {rp hp : HolProg 64} {link l1 l2 dest hs hl}
    (supported : executionSupported (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl))) = true) :
    executionSupported hp = true := by
  simp only [executionSupported, Bool.and_eq_true] at supported
  exact supported.2

#print axioms executionKindOfResult_result
#print axioms ExecutionResultValid.nonerror
#print axioms ExecutionResultValid.nontimeout
#print axioms executionSupported_seq
#print axioms executionSupported_ite
#print axioms executionSupported_loop
#print axioms executionSupported_return
#print axioms executionSupported_handler
end InitECandidate.Runtime.StackToLab

import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.PanDecCallReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every explicit returned pair starts with one of these literal tags.
Callee return values are consumed by declaration and handler-free calls. -/
def returnedPairTagSyntax (tags : List (BitVec 64)) : ProgHOL 64 → Bool
  | .dec _ _ _ body | .decCall _ _ _ _ body => returnedPairTagSyntax tags body
  | .seq first second => returnedPairTagSyntax tags first && returnedPairTagSyntax tags second
  | .ite _ yes no => returnedPairTagSyntax tags yes && returnedPairTagSyntax tags no
  | .return (.rstruct [.const tag,_]) => tags.contains tag
  | program => noDirectReturn program

theorem evaluate_returnedPairTagSyntax {F : Type} (tags : List (BitVec 64)) (program : ProgHOL 64)
    (supported : returnedPairTagSyntax tags program = true) (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s program = (some (.returned value),post)) :
    ∃ tag payload, tag ∈ tags ∧ value = .rStruct [.val (.word tag),payload] := by
  cases shape : program with
  | dec name kind initializer body =>
    rw [shape] at run
    obtain ⟨initial,output,_,bodyRun,_⟩ := evaluate_dec_returned_scope s post name kind initializer body value run
    exact evaluate_returnedPairTagSyntax tags body (by simpa only [shape,returnedPairTagSyntax] using supported) _ output value bodyRun
  | decCall name kind function arguments body =>
    rw [shape] at run
    obtain ⟨initial,ready,output,_,_,bodyRun,_⟩ := evaluate_decCall_returned_continuation s post name function kind arguments body value run
    exact evaluate_returnedPairTagSyntax tags body (by simpa only [shape,returnedPairTagSyntax] using supported) _ output value bodyRun
  | seq first second =>
    rw [shape] at run
    have children : returnedPairTagSyntax tags first = true ∧ returnedPairTagSyntax tags second = true := by
      simpa only [shape,returnedPairTagSyntax,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases firstRun : evaluateHOLFiniteState s first with
    | mk result next =>
      rw [firstRun] at run
      cases result with
      | none => exact evaluate_returnedPairTagSyntax tags second children.2 next post value run
      | some stopped =>
        have same := (Prod.mk.inj run).1
        simp only [Option.some.injEq] at same
        subst stopped
        exact evaluate_returnedPairTagSyntax tags first children.1 s next value firstRun
  | ite condition yes no =>
    rw [shape] at run
    have children : returnedPairTagSyntax tags yes = true ∧ returnedPairTagSyntax tags no = true := by
      simpa only [shape,returnedPairTagSyntax,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite] at run
    split at run
    · split at run
      · exact evaluate_returnedPairTagSyntax tags no children.2 s post value run
      · exact evaluate_returnedPairTagSyntax tags yes children.1 s post value run
    · cases run
  | «return» expression =>
    rw [shape] at run
    rw [shape] at supported
    cases expression <;> try simp [returnedPairTagSyntax,noDirectReturn] at supported
    case rstruct fields =>
      cases fields with
      | nil => simp [returnedPairTagSyntax,noDirectReturn] at supported
      | cons first rest =>
        cases first <;> try simp [returnedPairTagSyntax,noDirectReturn] at supported
        case const tag =>
          cases rest with
          | nil => simp [returnedPairTagSyntax,noDirectReturn] at supported
          | cons payload tail =>
            cases tail with
            | cons _ _ => simp [returnedPairTagSyntax,noDirectReturn] at supported
            | nil =>
              have member : tag ∈ tags := by simpa [returnedPairTagSyntax] using supported
              cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) payload with
              | none => simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,evaluated] at run
              | some payloadValue =>
                have result : (if sizeOfShapeWithContextHOL s.structs
                    (shapeOfHOLExact (.rStruct [.val (.word tag),payloadValue])) ≤ 32
                    then some (PanSemResultExact.returned (.rStruct [.val (.word tag),payloadValue]))
                    else some .error) = some (.returned value) := by
                  simpa [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,evaluated,apply_ite] using congrArg Prod.fst run
                split at result
                · exact ⟨tag,payloadValue,member,(PanSemResultExact.returned.inj (Option.some.inj result)).symm⟩
                · cases result
  | _ =>
    have noReturn : noDirectReturn program = true := by simpa only [shape,returnedPairTagSyntax] using supported
    exact False.elim ((evaluate_noDirectReturn program noReturn s value) (congrArg Prod.fst run))
termination_by sizeOf program

#print axioms evaluate_returnedPairTagSyntax
end InitECandidate.Runtime

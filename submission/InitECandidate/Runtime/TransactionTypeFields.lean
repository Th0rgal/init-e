import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.HashWordStep
import InitECandidate.Runtime.TransactionRequiredFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionTypeFieldCase (kind count : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "t")) (.const kind))
    (.assign .local (ofString "nfields") (.const count)) .skip

def transactionTypeFields : ProgHOL 64 :=
  .seq (transactionTypeFieldCase 1 11)
    (.seq (transactionTypeFieldCase 2 12)
      (.seq (transactionTypeFieldCase 3 14) (transactionTypeFieldCase 4 13)))

theorem evaluate_transaction_type_field_case {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind selected old count : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word old))) :
    evaluateHOLFiniteState state (transactionTypeFieldCase selected count) =
      (none,if kind = selected then setVarHOLFinite (ofString "nfields") (.val (.word count)) state else state) := by
  have assigned := evaluate_local_word_assignment state (ofString "nfields") (.const count) old count countLocal (by rfl)
  unfold transactionTypeFieldCase
  rw [evaluateHOLFiniteState_ite]
  by_cases same : kind = selected
  · subst kind
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "t")) (.const selected)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [condition]
    simpa only [ite_true,show (1 : BitVec 64) ≠ 0 by decide,ite_false] using assigned
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "t")) (.const selected)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,same]
    rw [condition]
    simp only [ite_true,if_neg same,evaluateHOLFiniteState_skip]

def transactionTypeParseBranch : ProgHOL 64 :=
  match transactionAt 9 with
  | .seq branch _ => branch
  | _ => .skip

def transactionTypedPath : ProgHOL 64 :=
  match transactionTypeParseBranch with
  | .ite _ yes _ => yes
  | _ => .skip

theorem source_transaction_typed_fields :
    authorizationNext (authorizationNext transactionTypedPath) = transactionTypeFields := by
  simp only [transactionTypedPath,transactionTypeParseBranch,transactionTypeFields,transactionTypeFieldCase,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_type_fields_result {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind : BitVec 64) (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64)))) :
    let output := evaluateHOLFiniteState state transactionTypeFields
    output.1 = none ∧ output.2.clock = state.clock ∧
      output.2.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) := by
  rcases supported with rfl | rfl | rfl | rfl | rfl <;>
    simp [transactionTypeFields,evaluateHOLFiniteState_seq_line780,evaluate_transaction_type_field_case,
      typeLocal,countLocal,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "nfields" ≠ ofString "t" by decide,transactionRequiredFields]

#print axioms source_transaction_typed_fields
#print axioms transaction_type_fields_result
#print axioms evaluate_transaction_type_field_case
end InitECandidate.Runtime

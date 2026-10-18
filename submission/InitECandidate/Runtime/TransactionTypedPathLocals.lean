import InitECandidate.Runtime.TransactionTypedDecodeSource
import InitECandidate.Runtime.TransactionTypeFieldsFrame
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal typed parsing assigns the type byte and its exact required field
count, independent of parsing success assumptions or memory-domain premises. -/
theorem transaction_typed_path_normal_type_count {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind oldKind : BitVec 64)
    (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word oldKind)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (run : evaluateHOLFiniteState state transactionTypedPath = (none,post)) :
    post.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      post.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) := by
  rw [source_transaction_typed_decode,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state
      (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionTypedDecodeArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have kept : ∀ name, name ≠ ofString "top" → middle.locals.lookup name = state.locals.lookup name := by
        intro name different
        apply evaluate_normalLocalFrame name _ _ state middle called
        simp [normalLocalFrameSyntax,Ne.symm different]
      have assigned := evaluate_local_word_assignment middle (ofString "t") (.var .local (ofString "b0")) oldKind kind
        ((kept _ (by decide)).trans typeLocal)
        (by simp [evalHOLExact,(kept _ (by decide)).trans byteLocal])
      let ready := setVarHOLFinite (ofString "t") (.val (.word kind)) middle
      have atType : ready.locals.lookup (ofString "t") = some (.val (.word kind)) := by
        simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have atCount : ready.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))) := by
        simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "t" ≠ ofString "nfields" by decide] using (kept _ (by decide)).trans countLocal
      change evaluateHOLFiniteState middle transactionTypeAssign = (none,ready) at assigned
      rw [evaluateHOLFiniteState_seq_line780,assigned] at run
      dsimp only at run
      have fields := transaction_type_fields_result ready kind supported atType atCount
      have frame := transaction_type_fields_frame ready
      rw [run] at fields frame
      exact ⟨(frame.2.2 _ (by decide)).trans atType,fields.2.2⟩

#print axioms transaction_typed_path_normal_type_count
end InitECandidate.Runtime

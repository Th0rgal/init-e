import InitECandidate.Runtime.RlpItemShortString
import InitECandidate.Runtime.RlpItemShortProgress
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The consumed-length progress guarantee survives the original n=b-128
scope, even when the caller already had an unrelated n binding. -/
theorem rlpItem_short_string_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183) (nonzero : total ≠ 0)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemShortString = (some (.returned value),post)) :
    (header - 128).toNat < total.toNat ∧ 0 < (1 + (header - 128)).toNat ∧
      (1 + (header - 128)).toNat ≤ total.toNat := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 128]) = some (.val (.word (header - 128))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_short_string] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "n")
    (.op .sub [.var .local (ofString "b"),.const 128]) (header - 128) rlpItemShortBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 128))) state
  have atPayload : entered.locals.lookup (ofString "n") = some (.val (.word (header - 128))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have small : (header - 128).toNat ≤ 55 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; exact lower)]
    change header.toNat - 128 ≤ 55
    omega
  exact rlpItem_short_return_progress entered output (header - 128) total value atPayload atTotal nonzero small code ticks bodyRun

/-- Returning from the original header dispatch retains the same bounded,
strictly positive consumed length as the selected short-string declaration. -/
theorem rlpItem_short_after_load_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183) (nonzero : total ≠ 0)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),post)) :
    (header - 128).toNat < total.toNat ∧ 0 < (1 + (header - 128)).toNat ∧
      (1 + (header - 128)).toNat ≤ total.toNat := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_lt.mpr lower,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  obtain ⟨result,output,bodyRun,_,_,_,terminal,_⟩ :=
    evaluate_rlpItem_short_string state pointer header pointerLocal headerLocal code ticks
  have selected : evaluateHOLFiniteState state rlpItemAfterByte = evaluateHOLFiniteState state rlpItemShortString := by
    rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first]
    dsimp only
    rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    rw [bodyRun]
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped => rfl
  apply rlpItem_short_string_return_progress state post header total value headerLocal totalLocal lower upper nonzero code ticks
  rw [← selected]
  exact run

#print axioms rlpItem_short_after_load_return_progress
#print axioms rlpItem_short_string_return_progress
end InitECandidate.Runtime

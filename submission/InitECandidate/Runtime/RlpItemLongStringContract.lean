import InitECandidate.Runtime.RlpItemLongReadContract
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.RlpItemLongDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful evaluation of the original long-string branch consumes a
positive prefix bounded by the input, with a strictly smaller payload. -/
theorem rlpItem_long_string_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongString = (some (.returned value),final)) :
    ∃ payload : BitVec 64, value = rlpItemLongValue pointer (header - 183) payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + ((header - 183) + payload)).toNat ∧
      (1 + ((header - 183) + payload)).toNat ≤ total.toNat := by
  have sizeBound := (rlp_long_string_length_bytes header lower upper).2
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_long_string] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpItemLongBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  exact rlpItem_long_body_return_contract entered output pointer (header - 183) total value
    atPointer atLength atTotal nonzero code (by change (header - 183).toNat + 2 ≤ state.clock; omega) bodyRun

/-- Header dispatch preserves the long-string consumption theorem for the
actual parser suffix following the header-byte load. -/
theorem rlpItem_long_after_load_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),final)) :
    ∃ payload : BitVec 64, value = rlpItemLongValue pointer (header - 183) payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + ((header - 183) + payload)).toNat ∧
      (1 + ((header - 183) + payload)).toNat ≤ total.toNat := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  have terminal := evaluate_rlpItem_long_string_terminal state pointer header pointerLocal headerLocal lower upper code ticks
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
  cases selected : evaluateHOLFiniteState state rlpItemLongString with
  | mk result post =>
    rw [selected] at terminal run
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped =>
      have equal := Prod.mk.inj run
      have stoppedEq := Option.some.inj equal.1
      subst stopped
      have postEq := equal.2
      subst post
      exact rlpItem_long_string_return_contract state final pointer header total value
        pointerLocal headerLocal totalLocal lower upper nonzero code (by omega) selected

#print axioms rlpItem_long_after_load_return_contract
#print axioms rlpItem_long_string_return_contract
end InitECandidate.Runtime

import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.KeyToNibblesOffsetPair
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scoped nibble writes followed by a read-only counter update. -/
inductive NibbleScopedWordFrame (width : Nat) : ProgHOL 64 → Prop
  | tail (program : ProgHOL 64) (readOnly : readOnlyMemory program = true) :
      NibbleScopedWordFrame width program
  | store (offset : Nat) (value : ExpHOL 64) {rest : ProgHOL 64}
      (inside : offset < width) (next : NibbleScopedWordFrame width rest) :
      NibbleScopedWordFrame width (.seq (.storeByte (keyNibbleOutputAddress offset) value) rest)
  | declare (name : MlS) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (notOut : name ≠ ofString "out") (notIndex : name ≠ ofString "i")
      (nested : NibbleScopedWordFrame width body) :
      NibbleScopedWordFrame width (.dec name .one initializer body)

/-- Neither inaccessible loads nor failed stores require an access-success
premise for a separate aligned word to remain unchanged. -/
theorem evaluate_nibbleScopedWordFrame {F : Type} {width : Nat} {program : ProgHOL 64}
    (supported : NibbleScopedWordFrame width program)
    (out index watched : BitVec 64)
    (separate : ∀ offset : Nat, offset < width →
      watched ≠ panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))) :
    ∀ state : PanSemStateFiniteExact 64 F,
      state.locals.lookup (ofString "out") = some (.val (.word out)) →
      state.locals.lookup (ofString "i") = some (.val (.word index)) →
      (evaluateHOLFiniteState state program).2.memory watched = state.memory watched := by
  induction supported with
  | tail program readOnly =>
    intro state atOut atIndex
    exact congrFun (evaluate_readOnly_memory program readOnly state) watched
  | store offset value inside next ih =>
    intro state atOut atIndex
    have address := (eval_keyNibble_offset_output state out index offset atOut atIndex).1
    have frame := evaluate_storeByte_memory_frame state (keyNibbleOutputAddress offset) value
      (out + (2 * index + BitVec.ofNat 64 offset)) watched address (separate offset inside)
    have control := evaluate_storeByte_control_frame state (keyNibbleOutputAddress offset) value
    rw [evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState state (.storeByte (keyNibbleOutputAddress offset) value) with
    | mk result middle =>
      rw [stored] at frame control
      dsimp only at frame control
      rcases control.1 with rfl | rfl
      · exact (ih middle (by rw [control.2.2.1]; exact atOut)
          (by rw [control.2.2.1]; exact atIndex)).trans frame
      · exact frame
  | declare name initializer notOut notIndex nested ih =>
    intro state atOut atIndex
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · rename_i value initialized
      split
      · have childOut : (setVarHOLFinite name value state).locals.lookup (ofString "out") = some (.val (.word out)) := by
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notOut] using atOut
        have childIndex : (setVarHOLFinite name value state).locals.lookup (ofString "i") = some (.val (.word index)) := by
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notIndex] using atIndex
        exact ih (setVarHOLFinite name value state) childOut childIndex
      · rfl
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_nibbleScopedWordFrame

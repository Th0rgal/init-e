import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def byteOffsetStoreAddress (key : MlS) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .var .local key else .op .add [.var .local key,.const (BitVec.ofNat 64 offset)]

def byteOffsetStorePlan (key : MlS) (stores : List (Nat × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  match stores with
  | [] => tail
  | (offset,value) :: rest => .seq (.storeByte (byteOffsetStoreAddress key offset) value)
      (byteOffsetStorePlan key rest tail)

theorem byteOffsetStorePlan_memory {F : Type} (key : MlS) (stores : List (Nat × ExpHOL 64))
    (tail : ProgHOL 64) (readOnly : readOnlyMemory tail = true)
    (state : PanSemStateFiniteExact 64 F) (pointer watched : BitVec 64)
    (localPointer : state.locals.lookup key = some (.val (.word pointer)))
    (separate : ∀ entry ∈ stores, watched ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 entry.1)) :
    (evaluateHOLFiniteState state (byteOffsetStorePlan key stores tail)).2.memory watched = state.memory watched := by
  induction stores generalizing state with
  | nil => exact congrFun (evaluate_readOnly_memory tail readOnly state) watched
  | cons entry rest ih =>
    obtain ⟨offset,value⟩ := entry
    have address : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (byteOffsetStoreAddress key offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
      by_cases zero : offset = 0
      · subst offset; simp [byteOffsetStoreAddress,evalHOLExact,localPointer]
      · simp [byteOffsetStoreAddress,zero,evalHOLExact,evalListHOLExact,localPointer,wordOpHOL,wordOp,valueIsWord,valueWord]
    have frame := evaluate_storeByte_memory_frame state _ value _ watched address (separate (offset,value) (by simp))
    have locals := (evaluate_storeByte_control_frame state (byteOffsetStoreAddress key offset) value).2.2.1
    rw [byteOffsetStorePlan,evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState state (.storeByte (byteOffsetStoreAddress key offset) value) with
    | mk result middle =>
      rw [stored] at frame locals
      cases result with
      | none =>
        exact (ih middle (by rw [locals]; exact localPointer)
          (fun entry member => separate entry (List.mem_cons_of_mem _ member))).trans frame
      | some result => exact frame

#print axioms byteOffsetStorePlan_memory
end InitECandidate.Runtime

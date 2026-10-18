import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def wordStorePlan (key : MlS) (stores : List (Nat × BitVec 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  match stores with
  | [] => tail
  | (offset,value) :: rest => .seq
      (.store (.op .add [.var .local key,.const (BitVec.ofNat 64 offset)]) (.const value))
      (wordStorePlan key rest tail)

theorem wordStorePlan_memory {F : Type} (key : MlS) (stores : List (Nat × BitVec 64))
    (tail : ProgHOL 64) (readOnly : readOnlyMemory tail = true)
    (state : PanSemStateFiniteExact 64 F) (pointer watched : BitVec 64)
    (localPointer : state.locals.lookup key = some (.val (.word pointer)))
    (separate : ∀ entry ∈ stores, watched ≠ pointer + BitVec.ofNat 64 entry.1) :
    (evaluateHOLFiniteState state (wordStorePlan key stores tail)).2.memory watched = state.memory watched := by
  induction stores generalizing state with
  | nil => exact congrFun (evaluate_readOnly_memory tail readOnly state) watched
  | cons entry rest ih =>
    obtain ⟨offset,value⟩ := entry
    have address : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.op .add [.var .local key,.const (BitVec.ofNat 64 offset)]) =
        some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
      simp [evalHOLExact,evalListHOLExact,localPointer,wordOpHOL,wordOp,valueIsWord,valueWord]
    have frame := evaluate_wordStore_memory_frame state _ (.const value) _ watched address
      (by intro parsed evaluated; simp only [evalHOLExact,Option.some.injEq] at evaluated; exact ⟨value,evaluated.symm⟩)
      (separate (offset,value) (by simp))
    have locals := (evaluate_store_control_frame state
      (.op .add [.var .local key,.const (BitVec.ofNat 64 offset)]) (.const value)).2.1
    rw [wordStorePlan,evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState state
        (.store (.op .add [.var .local key,.const (BitVec.ofNat 64 offset)]) (.const value)) with
    | mk result middle =>
      rw [stored] at frame locals
      cases result with
      | none =>
        exact (ih middle (by rw [locals]; exact localPointer)
          (fun entry member => separate entry (List.mem_cons_of_mem _ member))).trans frame
      | some result => exact frame

#print axioms wordStorePlan_memory
end InitECandidate.Runtime

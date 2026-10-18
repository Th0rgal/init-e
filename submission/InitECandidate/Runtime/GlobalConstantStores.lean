import InitECandidate.Runtime.DecodeRequestsStoresReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def globalConstantStores (name : MlS) : List (BitVec 64 × BitVec 64) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | (offset,value) :: rest, tail =>
      .seq (.store (.op .add [.var .global name,.const offset]) (.const value))
        (globalConstantStores name rest tail)

/-- A literal table initializer changes only its stated memory cells. Its
continuation sees the same clock, globals, locals, code and address domain. -/
theorem evaluate_globalConstantStores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer : BitVec 64) (cells : List (BitVec 64 × BitVec 64)) (tail : ProgHOL 64)
    (global : state.globals.lookup name = some (.val (.word pointer)))
    (domain : ∀ cell ∈ cells, state.memaddrs (pointer + cell.1)) :
    evaluateHOLFiniteState state (globalConstantStores name cells tail) =
      evaluateHOLFiniteState {state with memory := memWrites state.memory pointer cells} tail := by
  induction cells generalizing state with
  | nil => rfl
  | cons cell rest ih =>
    obtain ⟨offset,value⟩ := cell
    have address : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.op .add [.var .global name,.const offset]) = some (.val (.word (pointer + offset))) := by
      simp [evalHOLExact,evalListHOLExact,global,wordOpHOL,wordOp,valueIsWord,valueWord]
    have stored := sszStore_in state (pointer + offset) value _ (.const value) address
      (by simp [evalHOLExact]) (domain (offset,value) (by simp))
    rw [globalConstantStores,evaluateHOLFiniteState_seq_line780,stored]
    exact ih {state with memory := wmem state.memory (pointer + offset) value} global
      (fun cell member => domain cell (by simp [member]))

#print axioms evaluate_globalConstantStores
end InitECandidate.Runtime

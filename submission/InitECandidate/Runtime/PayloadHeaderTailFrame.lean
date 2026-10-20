import InitECandidate.Runtime.ActualPayloadHeaderBlockHashesWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- **Suffix frame contract for the `payload_header` serialization tail.**

`PayloadHeaderTailFrame F index watched` says: whenever the real statements from `index` run to a
returned value, a watched cell keeps its value.  This is the contract shape of the checked tail steps;
each index is discharged by a statement-level window proof over the actual source, and the chain is
built from `index = 51` down to `index = 40`. -/
def PayloadHeaderTailFrame (F : Type) (index : Nat) (watched : BitVec 64) : Prop :=
  ∀ (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64),
    evaluateHOLFiniteState state (actualPayloadHeaderAt index) = (some (.returned value),post) →
    post.memory watched = state.memory watched

/-- The tail's base case: the final statement is `return h`, which clears locals and writes nothing,
so it keeps every watched cell -- with no side condition at all (if `h` is unbound the statement
errors, so the returned-run hypothesis is vacuous). -/
theorem payloadHeaderTailFrame_return (F : Type) (watched : BitVec 64) :
    PayloadHeaderTailFrame F 51 watched := by
  intro state post value run
  rw [source_actual_payload_header_return,evaluateHOLFiniteState_return] at run
  cases hlook : state.locals.lookup (ofString "h") with
  | none =>
      rw [show @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) (.var .local (ofString "h")) = none from by
          simp [evalHOLExact,hlook]] at run
      obtain ⟨h1,_⟩ := Prod.mk.inj run
      cases h1
  | some held =>
      simp only [evalHOLExact,hlook] at run
      by_cases size : sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact held) ≤ 32
      · rw [if_pos size] at run
        obtain ⟨_,rfl⟩ := Prod.mk.inj run
        rfl
      · rw [if_neg size] at run
        obtain ⟨h1,_⟩ := Prod.mk.inj run
        cases h1

#print axioms payloadHeaderTailFrame_return

end InitECandidate.Runtime

import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte stores with destinations separated from a watched word, followed by
a memory-preserving tail. Store failures remain covered. -/
inductive BoundWordStoreChainFrame {F : Type} (bindings : HolFiniteMapExact MlS (ValueHOL 64))
    (watched : BitVec 64) : ProgHOL 64 → Prop
  | tail (program : ProgHOL 64) (supported : readOnlyMemory program = true) : BoundWordStoreChainFrame (F := F) bindings watched program
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (target : ∀ state : PanSemStateFiniteExact 64 F, state.locals = bindings → ∃ address : BitVec 64,
        @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)) ∧
        watched ≠ address)
      (wordValue : ∀ state : PanSemStateFiniteExact 64 F, state.locals = bindings → ∀ parsed,
        @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) value = some parsed →
        ∃ word : BitVec 64, parsed = .val (.word word))
      (next : BoundWordStoreChainFrame (F := F) bindings watched rest) :
      BoundWordStoreChainFrame (F := F) bindings watched (.seq (.store destination value) rest)

theorem evaluate_boundWordStoreChain_frame {F : Type} {bindings : HolFiniteMapExact MlS (ValueHOL 64)}
    {watched : BitVec 64} {program : ProgHOL 64} (supported : BoundWordStoreChainFrame (F := F) bindings watched program)
    (state : PanSemStateFiniteExact 64 F) (locals : state.locals = bindings) :
    (evaluateHOLFiniteState state program).2.memory watched = state.memory watched := by
  induction supported generalizing state with
  | tail program supported => exact congrFun (evaluate_readOnly_memory program supported state) watched
  | store destination value target wordValue next ih =>
    obtain ⟨address,addressEval,separate⟩ := target state locals
    have frame := evaluate_wordStore_memory_frame state destination value address watched addressEval (wordValue state locals) separate
    have control := evaluate_store_control_frame state destination value
    rw [evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState state (.store destination value) with
    | mk result middle =>
      rw [stored] at frame control
      dsimp only at frame control
      rcases control.1 with rfl | rfl
      · exact (ih middle (control.2.1.trans locals)).trans frame
      · exact frame

#print axioms evaluate_boundWordStoreChain_frame
end InitECandidate.Runtime

import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte stores with destinations separated from a watched word, followed by
a memory-preserving tail. Store failures remain covered. -/
inductive ByteStoreChainFrame {F : Type} (bindings : HolFiniteMapExact MlS (ValueHOL 64))
    (watched : BitVec 64) : ProgHOL 64 → Prop
  | tail (program : ProgHOL 64) (supported : readOnlyMemory program = true) : ByteStoreChainFrame (F := F) bindings watched program
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (target : ∀ state : PanSemStateFiniteExact 64 F, state.locals = bindings → ∃ address : BitVec 64,
        @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)) ∧
        watched ≠ panByteAlignHOL address)
      (next : ByteStoreChainFrame (F := F) bindings watched rest) :
      ByteStoreChainFrame (F := F) bindings watched (.seq (.storeByte destination value) rest)

theorem evaluate_byteStoreChain_frame {F : Type} {bindings : HolFiniteMapExact MlS (ValueHOL 64)}
    {watched : BitVec 64} {program : ProgHOL 64} (supported : ByteStoreChainFrame (F := F) bindings watched program)
    (state : PanSemStateFiniteExact 64 F) (locals : state.locals = bindings) :
    (evaluateHOLFiniteState state program).2.memory watched = state.memory watched := by
  induction supported generalizing state with
  | tail program supported => exact congrFun (evaluate_readOnly_memory program supported state) watched
  | store destination value target next ih =>
    obtain ⟨address,addressEval,separate⟩ := target state locals
    have frame := evaluate_storeByte_memory_frame state destination value address watched addressEval separate
    have control := evaluate_storeByte_control_frame state destination value
    rw [evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState state (.storeByte destination value) with
    | mk result middle =>
      rw [stored] at frame control
      dsimp only at frame control
      rcases control.1 with rfl | rfl
      · exact (ih middle (control.2.2.1.trans locals)).trans frame
      · exact frame

#print axioms evaluate_byteStoreChain_frame
end InitECandidate.Runtime

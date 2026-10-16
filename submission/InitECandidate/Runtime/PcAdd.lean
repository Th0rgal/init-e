import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def pcAddStoredPc : ExpHOL 64 :=
  .op .add [fundingLoad 0,.var .local (ofString "n")]

theorem source_pcAdd_body : sourceFunctionBody Guest.guestFn_pc_add =
    .seq (.store (fundingAddress 0) pcAddStoredPc) (.return (.const 0)) := by cbv

noncomputable def pcAddPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord state (frame + 0) (pc + amount))

theorem eval_pcAddStoredPc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "n") = some (.val (.word amount)))
    (domain : state.memaddrs (frame + 0)) (memory : state.memory (frame + 0) = .word pc) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) pcAddStoredPc =
      some (.val (.word (pc + amount))) := by
  classical
  unfold pcAddStoredPc
  simp only [evalHOLExact,evalListHOLExact]
  rw [eval_fundingLoad state frame 0 pc hFrame domain memory]
  simp [evalHOLExact,toExact,hAmount,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Complete authoritative pc_add body execution at any source clock. -/
theorem evaluate_source_pcAdd {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "n") = some (.val (.word amount)))
    (domain : state.memaddrs (frame + 0)) (memory : state.memory (frame + 0) = .word pc) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_pc_add) =
      (some (.returned (.val (.word 0))),pcAddPost state frame pc amount) := by
  classical
  rw [source_pcAdd_body]
  have store := evaluate_store_word state (frame + 0) (pc + amount) _ _
    (eval_fundingAddress state frame 0 hFrame)
    (eval_pcAddStoredPc state frame pc amount hFrame hAmount domain memory) domain
  apply evaluate_seq_none store
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,pcAddPost]

/-- Updating the frame PC cannot alias any of its funding cells. -/
theorem pcAddPost_funding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (pcAddPost state frame pc amount) frame funding := by
  simpa [HasGasFunding,pcAddPost,sourceWriteWord,emptyLocalsHOLFinite] using memory

#print axioms source_pcAdd_body
#print axioms evaluate_source_pcAdd
#print axioms pcAddPost_funding
end InitECandidate.Runtime

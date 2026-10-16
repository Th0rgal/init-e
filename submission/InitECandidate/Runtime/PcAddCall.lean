import InitECandidate.Runtime.PcAdd
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def pcAddCallPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64) : PanSemStateFiniteExact 64 F :=
  sourceWriteWord {state with clock := state.clock - 1} (frame + 0) (pc + amount)

/-- Exact ordinary pc_add call, including its one-clock debit and full frame. -/
theorem evaluate_pcAdd_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (frame pc amount : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word amount)])
    (installed : state.code.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : state.memaddrs (frame + 0)) (memory : state.memory (frame + 0) = .word pc) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "pc_add") [argument]) =
      (none,pcAddCallPost state frame pc amount) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word amount))
  let entry := callEntryStateHOLFinite state callee
  have argumentLocal : entry.locals.lookup (ofString "n") = some (.val (.word amount)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_source_pcAdd entry frame pc amount hFrame argumentLocal domain memory
  have lookup := pan_single_word_lookup state.code.lookup (ofString "pc_add") (ofString "n")
    (sourceFunctionBody Guest.guestFn_pc_add) amount installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "pc_add")
    [argument] [.val (.word amount)] (sourceFunctionBody Guest.guestFn_pc_add) callee .one
    (.val (.word 0)) (pcAddPost entry frame pc amount) arguments lookup clock body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

theorem pcAddCallPost_funding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (pcAddCallPost state frame pc amount) frame funding := by
  simpa [HasGasFunding,pcAddCallPost,sourceWriteWord] using memory

theorem pcAddCallPost_pc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame pc amount : BitVec 64) :
    (pcAddCallPost state frame pc amount).memory (frame + 0) = .word (pc + amount) := by
  simp [pcAddCallPost,sourceWriteWord]

#print axioms evaluate_pcAdd_call
#print axioms pcAddCallPost_funding
end InitECandidate.Runtime

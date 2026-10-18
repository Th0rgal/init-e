import InitECandidate.Runtime.RlpItemLongListReadReturn
import InitECandidate.Runtime.RlpItemLongListInputNamedGlobal
import InitECandidate.Runtime.PanDecCallReturnedGlobalClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_read_returned_named_global {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (pointer total headerLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (headerBound : headerLength.toNat ≤ 8)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) (value : ValueHOL 64)
    (evaluated : evaluateHOLFiniteState state rlpItemLongListRead = (some (.returned value),final)) :
    final.globals.lookup watched = state.globals.lookup watched := by
  let arguments : List (ExpHOL 64) := [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee := rlpReadLengthCallee (pointer + 1) headerLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "n") = some (.val (.word headerLength)) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ := evaluate_rlpReadLength_body_bounded entry
    (pointer + 1) headerLength atPointer atLength code (by change headerLength.toNat + 1 ≤ state.clock - 1; omega)
  have entryClock : entry.clock = state.clock - 1 := rfl
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) (pointer + 1) headerLength (by decide) installed
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_read_length)
  rw [run] at metadata
  dsimp only at metadata
  have callRun := evaluated
  rw [source_rlpItem_long_list_read] at callRun
  obtain ⟨parsed,actual,ready,output,actualRun,locals,globals,clock,domain,_,readyCode,tail,restored⟩ :=
    evaluate_decCall_returned_global_clock_scope state final (ofString "n") (ofString "rlp_read_length") .one .one
      arguments [.val (.word (pointer + 1)),.val (.word headerLength)]
      (sourceFunctionBody Guest.guestFn_rlp_read_length) rlpItemLongListFinish callee value args lookup callRun
  have same := Prod.mk.inj (run.symm.trans actualRun)
  have actualEq : post = actual := same.2
  subst actual
  obtain ⟨payload,rfl⟩ := returned parsed same.1
  let resumed := setVarHOLFinite (ofString "n") (.val (.word payload)) ready
  have atLL : resumed.locals.lookup (ofString "ll") = some (.val (.word headerLength)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "ll" by decide] using headerLocal
  have atTotal : resumed.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have atPayload : resumed.locals.lookup (ofString "n") = some (.val (.word payload)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atP : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "n" ≠ ofString "p" by decide] using pointerLocal
  have preserved := evaluate_rlpReadLength_body_frame entry code
  rw [run] at preserved
  have atScratch : resumed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals,preserved.2]
    exact scratchGlobal
  have atFrame : resumed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals,preserved.2]
    exact frameGlobal
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address low high
    change ready.memaddrs address
    rw [domain,metadata.2.1]
    exact arena address low high
  have result := rlpItem_long_list_uniform_finish_returned_named_global resumed output watched different pointer total headerLength payload scratch frame ceiling inputLimit
    atP atLL atPayload atTotal headerFits headerBound inputRange lengthBound limitBound atScratch atFrame
    (readyCode.trans (metadata.1.trans code)) orderedFrame framePositive scratchBelow resumedArena
    (by change total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1 ≤ ready.clock; rw [clock]; omega)
    value tail
  rw [restored]
  change output.globals.lookup watched = state.globals.lookup watched
  change output.globals.lookup watched = ready.globals.lookup watched at result
  rw [globals] at result
  exact result.trans (congrArg (fun g => g.lookup watched) preserved.2)

#print axioms rlpItem_long_list_read_returned_named_global
end InitECandidate.Runtime

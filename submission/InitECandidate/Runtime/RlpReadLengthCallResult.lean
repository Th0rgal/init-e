import InitECandidate.Runtime.RlpReadLengthBodyBound
import InitECandidate.Runtime.OriginalRlpReadLengthCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpReadLengthCallee (pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))

/-- Normal completion of the actual length-reader declaration-call binds a
word accumulator before executing its original caller continuation. -/
theorem evaluate_rlpReadLength_decCall_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : length.toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_read_length") arguments continuation) = (none,post)) :
    ∃ (word : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpReadLengthCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,_,_,_,returned⟩ := evaluate_rlpReadLength_body_bounded entry pointer length
    pointerLocal lengthLocal code (by change length.toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) pointer length (by decide) installed
  let property := fun value : ValueHOL 64 => ∃ word : BitVec 64, value = .val (.word word)
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_read_length) =
      (some (.returned value),output) → property value := by
    intro value output evaluated
    have same := (Prod.mk.inj (bodyRun.symm.trans evaluated)).1
    exact returned value same
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_return_property
    state post name (ofString "rlp_read_length") .one .one arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_read_length) continuation callee args lookup property bodyProperty run
  obtain ⟨word,rfl⟩ := valid
  exact ⟨word,ready,output,locals,tail,restored⟩

#print axioms evaluate_rlpReadLength_decCall_normal
end InitECandidate.Runtime

import InitECandidate.Runtime.RlpItemTotalBodyBound
import InitECandidate.Runtime.RlpItemTotalProgress
import InitECandidate.Runtime.PanDecCallReturnedBodyScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original item-total execution returns a positive, input-bounded
size. Header-result and declaration scopes are inverted from the actual run. -/
theorem rlpItemTotal_body_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total) = (some (.returned value),post)) :
    ∃ consumed : BitVec 64, value = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one])
    pointer length (by decide) installed
  rw [source_rlpItemTotal_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,_,_,_,_,tail,_⟩ := evaluate_decCall_returned_body_scope state post
    (ofString "h") (ofString "rlp_item_header") (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_header) rlpItemTotalContinuation
    (rlpHeaderCallee pointer length) value args lookup run
  let entry := callEntryStateHOLFinite state (rlpHeaderCallee pointer length)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTicks : 11 ≤ entry.clock := by change 11 ≤ state.clock - 1; omega
  have valid : RlpHeaderSizedProgress parsed length :=
    ⟨rlpHeader_uniform_return_progress entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun,
      rlpHeader_uniform_return_sizes entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun⟩
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst parsed
  apply rlpItemTotal_continuation_progress _ output header payload kind length value _ valid tail
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rlpItemTotal_body_progress
/-- Combined original body contract for callers: finite clock cost on every
outcome and positive bounded input consumption on every successful return. -/
theorem evaluate_rlpItemTotal_body_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 17 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total) = (result,post) ∧
      state.clock ≤ post.clock + ((2 * length.toNat + 1) * 15 + 17) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ consumed : BitVec 64,
        value = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat) := by
  have bound := evaluate_rlpItemTotal_body_bounded state pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total) with
  | mk result post =>
    rw [run] at bound
    refine ⟨result,post,rfl,bound.1,bound.2.1,bound.2.2,?_⟩
    intro value success
    apply rlpItemTotal_body_progress state post pointer length value pointerLocal lengthLocal code (by omega)
    rw [run,success]

#print axioms evaluate_rlpItemTotal_body_contract
end InitECandidate.Runtime

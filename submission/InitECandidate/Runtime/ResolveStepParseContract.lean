import InitECandidate.Runtime.ResolveStepParseBound
import InitECandidate.Runtime.RlpItemBodyRuntimeContract
import InitECandidate.Runtime.RlpItemBodyAbove
import InitECandidate.Runtime.PanLocalCallCodeTerminalHandlerNormal
import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resolve_step_parse_call_normal_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : resolveStepParseCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s resolveStepParseCall = (none,post)) :
    ∃ kind payloadPointer payload consumed : BitVec 64,
      post.locals = s.locals.update (ofString "it",
        .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) ∧
      pointer.toNat ≤ payloadPointer.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ payload.toNat ≤ length.toNat ∧
      (∀ watched, post.globals.lookup watched = s.globals.lookup watched) ∧
      (∀ watched : BitVec 64, ceiling ≤ watched.toNat → post.memory watched = s.memory watched) ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item)
    (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [source_resolve_step_parse_call] at run
  have normal := evaluate_localCall_code_terminal_handler_normal_result s post (ofString "it")
    (ofString "rlp_item") (.comb [.one,.one,.one,.one]) _ _ (sourceFunctionBody Guest.guestFn_rlp_item)
    (.call (some (none,none)) (ofString "mpt_fail") [.const 3]) (ofString "RlpErr") (ofString "e") callee
    args lookup (by
      intro current installed
      exact evaluate_mptFail_call_terminal current (.const 3) 3 (installed.trans code) (by rfl)) run
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result s post (ofString "it")
    (ofString "rlp_item") (.comb [.one,.one,.one,.one]) _ _ (sourceFunctionBody Guest.guestFn_rlp_item)
    callee args lookup normal
  have ticks : length.toNat * ((2*length.toNat+1)*15+19)+92632 ≤ entry.clock := by
    change _ ≤ s.clock-1
    unfold resolveStepParseCost at budget
    omega
  obtain ⟨kind,pp,payload,consumed,shape,starts,ends,nowrap,small,scratchPost,framePost,heapPost⟩ :=
    rlpItem_body_returned_runtime_contract entry bodyPost pointer length scratch frame ceiling inputLimit p n
      inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  refine ⟨kind,pp,payload,consumed,?_,starts,ends,nowrap,small,?_,?_,?_,?_,?_⟩
  · rw [restored,shape]
    rfl
  · intro watched
    rw [restored]
    by_cases same : watched = ofString "scratch_ptr"
    · subst watched
      exact scratchPost.trans scratchGlobal.symm
    · exact rlpItem_body_returned_named_global entry bodyPost watched (Ne.symm same) pointer length scratch frame
        ceiling inputLimit p n inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena ticks value bodyRun
  · intro watched above
    rw [restored]
    exact rlpItem_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit p n
      inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      ticks value bodyRun watched above
  · rw [restored]; exact metadata.1
  · rw [restored]; exact metadata.2.1
  · rw [restored]; exact metadata.2.2.1

#print axioms resolve_step_parse_call_normal_contract
end InitECandidate.Runtime

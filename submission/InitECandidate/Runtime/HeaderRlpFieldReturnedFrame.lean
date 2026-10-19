import InitECandidate.Runtime.HeaderRlpFieldBound
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.RlpItemBodyAbove
import InitECandidate.Runtime.RlpItemBodyGlobals
import InitECandidate.Runtime.RlpItemBodyNamedGlobal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem header_rlp_field_tail_readOnly (field : HeaderRlpField) : readOnlyMemory (headerRlpFieldTail field) = true := by
  cases field <;> rfl

/-- Returned raw/bytes/uint header-field parsers preserve the actual globals
and every old word above the scratch ceiling, including the slice table. -/
theorem header_rlp_field_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F) (field : HeaderRlpField)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) headerRlpFieldArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ s.clock)
    (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody (headerRlpFieldDeclaration field)) = (some (.returned v),post)) :
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ name : MlS, post.globals.lookup name = s.globals.lookup name) ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = s.memory address) := by
  have fullMetadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody (headerRlpFieldDeclaration field))
  rw [run] at fullMetadata
  rw [source_header_rlp_field] at run
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite s callee
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  obtain ⟨item,bodyPost,ready,output,bodyRun,_,readyMemory,readyGlobals,_,_,_,_,tail,restored⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope s post (ofString "it") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) headerRlpFieldArguments _
      (sourceFunctionBody Guest.guestFn_rlp_item) (headerRlpFieldTail field) callee v args lookup run
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ entry.clock := by
    change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ s.clock - 1
    omega
  have tailMemory := evaluate_readOnly_memory (headerRlpFieldTail field) (header_rlp_field_tail_readOnly field)
    (setVarHOLFinite (ofString "it") item ready)
  have tailGlobals := evaluate_readOnly_globals (headerRlpFieldTail field) (header_rlp_field_tail_readOnly field)
    (setVarHOLFinite (ofString "it") item ready)
  rw [tail] at tailMemory tailGlobals
  have postMemory : post.memory = bodyPost.memory := by
    rw [restored]
    exact tailMemory.trans readyMemory
  have postGlobals : post.globals = bodyPost.globals := by
    rw [restored]
    exact tailGlobals.trans readyGlobals
  refine ⟨fullMetadata.2.1,fullMetadata.1,?_,?_⟩
  · intro name
    rw [postGlobals]
    by_cases same : name = ofString "scratch_ptr"
    · subst name
      have kept := rlpItem_body_returned_globals entry bodyPost pointer length scratch frame ceiling inputLimit
        atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
        arena bodyBudget item bodyRun
      exact kept.1.trans scratchGlobal.symm
    · exact rlpItem_body_returned_named_global entry bodyPost name (Ne.symm same) pointer length scratch frame ceiling inputLimit
        atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
        arena bodyBudget item bodyRun
  · intro address above
    rw [postMemory]
    exact rlpItem_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit atPointer atLength noWrap
      lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget item bodyRun address above

#print axioms header_rlp_field_tail_readOnly
#print axioms header_rlp_field_returned_frame
end InitECandidate.Runtime

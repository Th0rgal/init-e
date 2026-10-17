import InitECandidate.Runtime.RlpDecodeFullyDeclarationBound
import InitECandidate.Runtime.RlpDecodeFullyBodyGlobals
import InitECandidate.Runtime.PanDecCallNormalGlobalClockScope
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal full-decoder declarations preserve scratch/frame globals through
caller continuations whose checked syntax cannot write globals. -/
theorem rlpDecodeFully_declaration_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : readOnlyMemory continuation = true)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one,.one,.one]) (ofString "rlp_decode_fully") arguments continuation) = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_decode_fully,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_decode_fully")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_decode_fully) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  obtain ⟨value,bodyPost,ready,output,bodyRun,_,globals,_,_,_,_,tail,restored⟩ := evaluate_decCall_normal_global_clock_scope state post name
    (ofString "rlp_decode_fully") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully) continuation callee args lookup run
  have bodyGlobals := rlpDecodeFully_body_returned_globals entry bodyPost pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega) value bodyRun
  have continuationGlobals := evaluate_readOnly_globals continuation supported (setVarHOLFinite name value ready)
  rw [tail] at continuationGlobals
  rw [restored]
  change output.globals.lookup _ = _ ∧ output.globals.lookup _ = _
  change output.globals = ready.globals at continuationGlobals
  rw [continuationGlobals,globals]
  exact bodyGlobals

#print axioms rlpDecodeFully_declaration_normal_globals
end InitECandidate.Runtime

import InitECandidate.Runtime.WorkspaceGlobalsKeep
import InitECandidate.Runtime.HeaderDecoderBodyOuterTable
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A successful installed assignment call exposes the actual header record
in its caller local and retains the older witness table and bounded workspace. -/
theorem header_decoder_call_normal_outer_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerDecoderBodyCost inputLimit + 1 ≤ s.clock)
    (older olderCount outerInput outerLength : BitVec 64)
    (olderTable : RlpSliceInputPrefix s older outerInput outerLength olderCount.toNat)
    (olderAbove : ceiling ≤ older.toNat)
    (olderBefore : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "decode_header") arguments) = (none,post)) :
    ∃ count : BitVec 64,
      count.toNat ≤ length.toNat ∧ count.toNat ≤ 23 ∧ post.locals = s.locals.update (name,.val (.word (allocationEnd array (count * 16)))) ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (allocationEnd array (count * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd array (count * 16)) 248).toNat ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → post.memory address = s.memory address) ∧
      RlpSliceInputPrefix post older outerInput outerLength olderCount.toNat ∧
      (∀ global : MlS, global ∈ parserWorkspaceGlobals → post.globals.lookup global = s.globals.lookup global) := by
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "decode_header") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_header) .one pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeHeader_lookup)
  obtain ⟨value,bodyPost,bodyRun,checked,resumed⟩ := evaluate_localCall_normal_result s post name (ofString "decode_header") .one
    arguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_decode_header)
    (rlpHeaderCallee pointer length) args lookup run
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have olderEntry : RlpSliceInputPrefix entry older outerInput outerLength olderCount.toNat :=
    olderTable.after_memory_below s entry older olderCount outerInput outerLength array olderBefore rfl (fun _ _ => rfl)
  obtain ⟨count,countBound,countSmall,valueEq,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory,retained⟩ :=
    header_decoder_body_returned_outer_table entry bodyPost pointer length scratch frame array ceiling inputLimit p len noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      ceilingAligned inputAfter inputBeforeArray (by change headerDecoderBodyCost inputLimit ≤ s.clock - 1; omega)
      older olderCount outerInput outerLength olderEntry olderAbove olderBefore value bodyRun
  rw [resumed]
  refine ⟨count,countBound,countSmall,?_,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory,?_,?_⟩
  · change s.locals.update (name,value) = _
    rw [valueEq]
  · exact retained.after_memory_below bodyPost _ older olderCount outerInput outerLength array olderBefore rfl (fun _ _ => rfl)
  · intro global member
    have kept := header_decoder_keeps_parser_workspace entry global member code
    rw [bodyRun] at kept
    exact kept

#print axioms header_decoder_call_normal_outer_table
end InitECandidate.Runtime

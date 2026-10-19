import InitECandidate.Runtime.WorkspaceGlobalsKeep
import InitECandidate.Runtime.HeaderDecoderCallNormalOuterTable
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A real decoder declaration reaches its continuation with the allocated
header and preserved witness table, or terminates within the installed call budget. -/
theorem header_decoder_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (continuation : ProgHOL 64) :
    Reaches s (.decCall name .one (ofString "decode_header") arguments continuation)
      (fun ready => ∃ count : BitVec 64,
      count.toNat ≤ length.toNat ∧ count.toNat ≤ 23 ∧ ready.locals = s.locals.update (name,.val (.word (allocationEnd array (count * 16)))) ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
      ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
      (allocationEnd array (count * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd array (count * 16)) 248).toNat ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → ready.memory address = s.memory address) ∧
      RlpSliceInputPrefix ready older outerInput outerLength olderCount.toNat ∧
      (∀ global : MlS, global ∈ parserWorkspaceGlobals → ready.globals.lookup global = s.globals.lookup global))
      (headerDecoderBodyCost inputLimit + 1) continuation := by
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "decode_header") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_header) .one pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeHeader_lookup)
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have olderEntry : RlpSliceInputPrefix entry older outerInput outerLength olderCount.toNat :=
    olderTable.after_memory_below s entry older olderCount outerInput outerLength array olderBefore rfl (fun _ _ => rfl)
  have bodyBudget : headerDecoderBodyCost inputLimit ≤ entry.clock := by
    change headerDecoderBodyCost inputLimit ≤ s.clock - 1
    omega
  have bounded := runBounded_decode_header_body entry pointer length scratch frame array ceiling inputLimit p len noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    ceilingAligned inputAfter inputBeforeArray bodyBudget
  apply bounded_decCall_reaches s name (ofString "decode_header") .one .one arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_decode_header) continuation
    (rlpHeaderCallee pointer length) (headerDecoderBodyCost inputLimit) _ args lookup budget bounded
  intro value bodyPost bodyRun checked
  obtain ⟨count,countBound,countSmall,valueEq,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory,retained⟩ :=
    header_decoder_body_returned_outer_table entry bodyPost pointer length scratch frame array ceiling inputLimit p len noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      ceilingAligned inputAfter inputBeforeArray bodyBudget older olderCount outerInput outerLength olderEntry olderAbove olderBefore value bodyRun
  refine ⟨count,countBound,countSmall,?_,extent,heapBinding,scratchBinding,frameBinding,domain,installed,recordExtent,cap,aligned,memory,?_,?_⟩
  · change s.locals.update (name,value) = _
    rw [valueEq]
  · exact retained.after_memory_below bodyPost _ older olderCount outerInput outerLength array olderBefore rfl (fun _ _ => rfl)
  · intro global member
    have kept := header_decoder_keeps_parser_workspace entry global member code
    rw [bodyRun] at kept
    exact kept

#print axioms header_decoder_declaration_reaches
end InitECandidate.Runtime

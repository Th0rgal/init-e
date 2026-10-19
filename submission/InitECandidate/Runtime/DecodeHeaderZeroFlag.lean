import InitECandidate.Runtime.DecodeHeaderFlagWhole
import InitECandidate.Runtime.DecodeHeaderTableEntryReach
import InitECandidate.Runtime.DecodeHeaderFieldsEntryReach
import InitECandidate.Runtime.DecodeHeaderFirstFieldStoreReach
/-!
The whole actual header decoder from the body entry `decodeHeaderAt 0`.

The prefix of the frozen body is three actual stretches: the slice entry to the field
table (`decodeHeaderAt 0 -> 5`, which already delivers the accepted array-allocation
coverage `array + count * 16 <= allocationEnd array (count * 16)`), the count guard with
the record allocation and the `is_current` store (`5 -> 9`), and the first field with its
record store (`9 -> 11`).

`decode_header_zero_flag` joins them and records everything the rest of the body needs:
the count and `is_current` witnesses, the allocated record pointer, the readable slice
table, the decoder locals of the entry state, the record geometry, the phase environment
`HeaderCarryEnv` against the reached state, and the zero-test invariant
`is_current != 0 -> 23 <= count`.

Composing it with `decode_header_whole_body_flag` gives the returned-header contract from
the body's own entry point: the returned value is the record pointer, the generated state
root word is readable at `pointer + 32`, the record domain and the code are those of the
entry state, every global but `heap_ptr` (the allocation) is unchanged, and the record
geometry holds.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The budget of the actual decoder prefix `decodeHeaderAt 0 -> 11`. -/
def headerPrefixCost (inputLimit : Nat) : Nat :=
  (decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit) +
    (2 + (headerRlpFieldCost inputLimit + 1))

/-- The accepted count guard yields at least twenty-one fields. -/
theorem header_count_twenty_one {count flag : BitVec 64}
    (accepted : (count = 21#64 ∧ flag = 0#64) ∨ (count = 23#64 ∧ flag = 1#64)) : 21 ≤ count.toNat := by
  rcases accepted with ⟨same,_⟩ | ⟨same,_⟩
  · exact same.symm ▸ (by decide : 21 ≤ (21#64).toNat)
  · exact same.symm ▸ (by decide : 21 ≤ (23#64).toNat)

/-- The accepted count guard yields a positive field count. -/
theorem header_count_positive {count flag : BitVec 64}
    (accepted : (count = 21#64 ∧ flag = 0#64) ∨ (count = 23#64 ∧ flag = 1#64)) : 0 < count.toNat := by
  rcases accepted with ⟨same,_⟩ | ⟨same,_⟩
  · exact same.symm ▸ (by decide : 0 < (21#64).toNat)
  · exact same.symm ▸ (by decide : 0 < (23#64).toNat)

/-- A current header (`is_current != 0`) has twenty-three fields. -/
theorem header_count_current {count flag : BitVec 64}
    (accepted : (count = 21#64 ∧ flag = 0#64) ∨ (count = 23#64 ∧ flag = 1#64)) :
    flag ≠ 0 → 23 ≤ count.toNat := by
  intro nonzero
  rcases accepted with ⟨_,zero⟩ | ⟨same,_⟩
  · exact absurd zero nonzero
  · exact same.symm ▸ (by decide : 23 ≤ (23#64).toNat)

/-- What the actual decoder prefix delivers at `decodeHeaderAt 11`. -/
def HeaderPrefixEntry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat) : Prop :=
  ∃ count flag record : BitVec 64, 21 ≤ count.toNat ∧ ((count = 21 ∧ flag = 0#64) ∨ (count = 23 ∧ flag = 1#64)) ∧
    post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
    post.locals.lookup (ofString "h") = some (.val (.word record)) ∧
    post.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
    HeaderCarryEnv post array count input inputLength scratch frame record ceiling inputLimit ∧
    (flag ≠ 0 → 23 ≤ count.toNat) ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
    post.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr") ∧
    post.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248)))

/-- The actual decoder prefix from the body entry reaches `decodeHeaderAt 11` with the
count, the `is_current` value, the allocated record, the readable slice table, the record
geometry and the phase environment. -/
theorem decode_header_zero_flag {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerPrefixCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 0)
      (fun post => HeaderPrefixEntry s post array pointer length scratch frame ceiling inputLimit)
      (headerPrefixCost inputLimit) (decodeHeaderAt 11) := by
  suffices intermediate : Reaches s (decodeHeaderAt 0)
      (fun post => ∃ count flag record : BitVec 64, 21 ≤ count.toNat ∧ ((count = 21 ∧ flag = 0#64) ∨ (count = 23 ∧ flag = 1#64)) ∧
        post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        post.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        post.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
        RlpSliceInputPrefix post array pointer length count.toNat ∧
        (flag ≠ 0 → 23 ≤ count.toNat) ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
        post.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr") ∧
        array.toNat + count.toNat * 16 ≤ record.toNat ∧ record.toNat + 248 < 2^64 ∧
        post.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))))
      (headerPrefixCost inputLimit) (decodeHeaderAt 11) by
    refine reaches_mono s (decodeHeaderAt 0) (decodeHeaderAt 11) _ _ _ _ (le_refl _) ?_ intermediate
    intro post facts
    obtain ⟨count,flag,record,countTwentyOne,accepted,atArray,atRecord,atFlag,table,currentBound,domainPost,codePost,
      scratchPost,framePost,geometry,recordFits,heapPost⟩ := facts
    have above : ceiling ≤ array.toNat := by omega
    have fits : array.toNat + count.toNat * 16 ≤ 2^64 := by omega
    have arenaPost : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling →
        post.memaddrs address := by
      intro address low high
      rw [domainPost]
      exact arena address low high
    exact ⟨count,flag,record,countTwentyOne,accepted,atArray,atRecord,atFlag,table,
      ⟨countTwentyOne,geometry,recordFits,above,fits,lengthBound,limitBound,scratchPost.trans scratchGlobal,
        framePost.trans frameGlobal,codePost.trans code,orderedFrame,framePositive,scratchBelow,arenaPost⟩,
      currentBound,domainPost,codePost,scratchPost,framePost,heapPost⟩
  unfold headerPrefixCost at budget
  have first := decode_header_table_entry_reaches s pointer length scratch frame array ceiling inputLimit atPointer
    atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena ceilingAligned inputAfter inputBeforeArray (by omega)
  apply reaches_trans_budget s (decodeHeaderAt 0) (decodeHeaderAt 5) (decodeHeaderAt 11) _ _
    (decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit)
    (2 + (headerRlpFieldCost inputLimit + 1)) (by omega) first
  intro entry factsEntry remaining
  obtain ⟨count,countBound,arrEntry,nEntry,tableEntry,heapEntry,scratchEntry,frameEntry,domainEntry,codeEntry,
    beforeTable,heapCap,heapAligned⟩ := factsEntry
  have nineReach : Reaches entry (decodeHeaderAt 5)
      (fun post => ∃ flag : BitVec 64,
        ((count = 21#64 ∧ flag = 0#64) ∨ (count = 23#64 ∧ flag = 1#64)) ∧
        post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        post.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
        post.locals.lookup (ofString "h") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        RlpSliceInputPrefix post array pointer length count.toNat ∧
        post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
        (allocationEnd array (count * 16)).toNat + 248 < 2^64 ∧
        post.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))))
      2 (decodeHeaderAt 9) := by
    refine reaches_mono entry (decodeHeaderAt 5) (decodeHeaderAt 9) _ _ _ _ (le_refl _) ?_
      (decode_header_fields_entry_reaches entry array count pointer length (allocationEnd array (count * 16))
        (codeEntry.trans code) arrEntry nEntry heapEntry tableEntry beforeTable heapCap (by omega))
    intro post facts
    obtain ⟨current,accepted,atArr,atN,atFlag,atH,table,memaddrs,codeFact,heapFact,other,extent,cap,al,memory⟩ := facts
    have scratchFact : post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
      (other (ofString "scratch_ptr") (by decide)).trans scratchEntry
    have frameFact : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
      (other (ofString "frame_mem_ptr") (by decide)).trans frameEntry
    have recordFits : (allocationEnd array (count * 16)).toNat + 248 < 2^64 := by omega
    exact ⟨current,accepted,atArr,atFlag,atH,table,memaddrs.trans domainEntry,codeFact.trans codeEntry,
      scratchFact,frameFact,beforeTable,recordFits,heapFact⟩
  apply reaches_trans_budget entry (decodeHeaderAt 5) (decodeHeaderAt 9) (decodeHeaderAt 11) _ _
    2 (headerRlpFieldCost inputLimit + 1) (by omega) nineReach
  intro guard factsGuard remainingGuard
  obtain ⟨current, factsGuard⟩ := factsGuard
  obtain ⟨accepted, arrGuard, flagGuard, recordGuard, tableGuard, domainGuard, codeGuard, scratchGuard,
    frameGuard, geometry, recordFits, heapGuard⟩ := factsGuard
  have positive : 0 < count.toNat := header_count_positive accepted
  have countTwentyOne : 21 ≤ count.toNat := header_count_twenty_one accepted
  have currentBound : current ≠ 0 → 23 ≤ count.toNat := header_count_current accepted
  have above : ceiling ≤ array.toNat := by omega
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := by omega
  refine reaches_mono guard (decodeHeaderAt 9) (decodeHeaderAt 11) _ _ _ _ (le_refl _) ?_
    (decode_header_first_field_store_reaches guard array count pointer length scratch frame
      (allocationEnd array (count * 16)) ceiling inputLimit arrGuard recordGuard
      geometry recordFits tableGuard positive above fits lengthBound limitBound scratchGuard frameGuard
      (codeGuard.trans code) orderedFrame framePositive scratchBelow
      (fun address low high => by rw [domainGuard]; exact arena address low high) (by omega))
  intro post facts
  obtain ⟨shape,localsPost,tablePost,domainPost,codePost,globalsPost,memoryPost⟩ := facts
  have atArrayPost : post.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [localsPost]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using arrGuard
  have atRecordPost : post.locals.lookup (ofString "h") =
      some (.val (.word (allocationEnd array (count * 16)))) := by
    rw [localsPost]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using recordGuard
  have atFlagPost : post.locals.lookup (ofString "is_current") = some (.val (.word current)) := by
    rw [localsPost]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using flagGuard
  have scratchPost : post.globals.lookup (ofString "scratch_ptr") = (some (.val (.word scratch))) :=
    (globalsPost (ofString "scratch_ptr")).trans scratchGuard
  have framePost : post.globals.lookup (ofString "frame_mem_ptr") = (some (.val (.word frame))) :=
    (globalsPost (ofString "frame_mem_ptr")).trans frameGuard
  refine ⟨count,current,allocationEnd array (count * 16),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact countTwentyOne
  · exact accepted
  · exact atArrayPost
  · exact atRecordPost
  · exact atFlagPost
  · exact tablePost
  · exact currentBound
  · exact domainPost.trans domainGuard
  · exact codePost.trans codeGuard
  · exact scratchPost.trans (scratchGlobal.symm)
  · exact framePost.trans (frameGlobal.symm)
  · exact geometry
  · exact recordFits
  · exact (globalsPost (ofString "heap_ptr")).trans heapGuard

#print axioms decode_header_zero_flag

/-- The whole actual header decoder from `decodeHeaderAt 0` to the actual return: for
either header kind, the returned value is the record pointer and the generated state root
word is readable at `pointer + 32`.  The record domain, the code, the frame globals and
the record geometry survive. -/
theorem decode_header_returned_root_from_zero {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerPrefixCost inputLimit + headerWholeBodyCost inputLimit ≤ s.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeHeaderAt 0) = (some (.returned value),post)) :
    ∃ count flag record : BitVec 64, value = .val (.word record) ∧ 21 ≤ count.toNat ∧
      count.toNat ≤ 23 ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
      (∃ word : BitVec 64, post.memory (record + 32#64) = .word word) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
      post.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr") ∧
      array.toNat + 21 * 16 ≤ record.toNat ∧ record.toNat + 248 < 2^64 := by
  have started := decode_header_zero_flag s pointer length scratch frame array ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap
    arrayBound countLimit heapArena ceilingAligned inputAfter inputBeforeArray (by omega)
  have total : Reaches s (decodeHeaderAt 0)
      (fun final => ∃ mid : PanSemStateFiniteExact 64 F, ∃ count flag record rooted : BitVec 64,
        HeaderSuffixCarry mid final array count pointer length record rooted ∧
        array.toNat + 21 * 16 ≤ record.toNat ∧ record.toNat + 248 < 2^64 ∧
        mid.memaddrs = s.memaddrs ∧ mid.code = s.code ∧
        mid.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
        mid.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr") ∧
        21 ≤ count.toNat ∧ ((count = 21 ∧ flag = 0#64) ∨ (count = 23 ∧ flag = 1#64)) ∧
        mid.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))))
      (headerPrefixCost inputLimit + headerWholeBodyCost inputLimit) (decodeHeaderAt 57) := by
    apply reaches_trans_budget s (decodeHeaderAt 0) (decodeHeaderAt 11) (decodeHeaderAt 57) _ _
      (headerPrefixCost inputLimit) (headerWholeBodyCost inputLimit) (by omega) started
    intro mid facts remaining
    obtain ⟨count,current,record,countTwentyOne,accepted,atArray,atRecord,atFlag,table,env,currentBound,domainMid,
      codeMid,scratchMid,frameMid,heapMid⟩ := facts
    refine reaches_mono mid (decodeHeaderAt 11) (decodeHeaderAt 57) _ _ _ _ (le_refl _) ?_
      (decode_header_whole_body_flag mid array count pointer length scratch frame record current ceiling inputLimit env
        atArray atRecord table atFlag currentBound (by omega))
    intro final kept
    obtain ⟨rooted,carried⟩ := kept
    exact ⟨mid,count,current,record,rooted,carried,(by have h := env.before; omega),env.recordFits,domainMid,codeMid,scratchMid,frameMid,
      countTwentyOne,accepted,heapMid⟩
  obtain ⟨ready,facts,_,_,agreement,returnedTail⟩ := reaches_returned_continuation s (decodeHeaderAt 0)
    (decodeHeaderAt 57) _ _ value total (by rw [run])
  obtain ⟨mid,facts⟩ := facts
  obtain ⟨count,current,record,rooted,facts⟩ := facts
  obtain ⟨carry,geometry,recordFits,domainMid,codeMid,scratchMid,frameMid,countTwentyOne,acceptedMid,
    heapMid⟩ := facts
  have countBound : count.toNat ≤ 23 := by
    rcases acceptedMid with ⟨eq,_⟩ | ⟨eq,_⟩ <;> rw [eq] <;> decide
  obtain ⟨rootMem,domain,codeEq,globals,_,_,atRecordReady⟩ := carry
  have tailMemory : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.memory = ready.memory := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have tailGlobals : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.globals = ready.globals := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have sourceMemory := agreement.2.2.1
  have sourceGlobals := agreement.2.2.2.1
  rw [run] at sourceMemory sourceGlobals
  have metadata := evaluateHOLFiniteState_metadata s (decodeHeaderAt 0)
  rw [run] at metadata
  refine ⟨count,current,record,?_,countTwentyOne,countBound,?_,⟨rooted,?_⟩,metadata.2.1,metadata.1,?_,?_,
    geometry,recordFits⟩
  · rw [source_decode_header_return,evaluateHOLFiniteState_return] at returnedTail
    simpa [evalHOLExact,atRecordReady,shapeOfHOLExact] using returnedTail.symm
  · rw [sourceGlobals,tailGlobals]
    exact (globals (ofString "heap_ptr")).trans heapMid
  · rw [sourceMemory,tailMemory]
    exact rootMem
  · rw [sourceGlobals,tailGlobals]
    exact (globals (ofString "scratch_ptr")).trans scratchMid
  · rw [sourceGlobals,tailGlobals]
    exact (globals (ofString "frame_mem_ptr")).trans frameMid

#print axioms decode_header_returned_root_from_zero
end InitECandidate.Runtime

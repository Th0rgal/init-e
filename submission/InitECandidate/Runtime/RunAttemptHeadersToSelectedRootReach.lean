import InitECandidate.Runtime.RunAttemptHeaderCountWindowReach
import InitECandidate.Runtime.RunAttemptHeadersDeclarationParentRoot
import InitECandidate.Runtime.RunAttemptSelectedParentRootReach
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual header call, count guard, parent load and global assignments
reach database construction with the selected parent state root and live heap. -/
theorem run_attempt_headers_to_selected_root_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapUpper : heap.toNat≤33805910000)
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 2)
      (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ liveHeap parent root : BitVec 64,
        RunAttemptHeaderValidationFacts s validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count≠0 ∧
        final=setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))) ∧
        final.locals.lookup (ofString "parent")=some (.val (.word parent)) ∧
        final.globals.lookup (ofString "heap_ptr")=some (.val (.word liveHeap)) ∧
        final.memory (parent+32#64)=.word root ∧ final.memaddrs (parent+32#64) ∧
        parent.toNat+248≤liveHeap.toNat ∧
        (allocationEnd heap (validateHeadersHsSize count)).toNat+count.toNat*32+32≤parent.toNat)
      (validateHeadersBodyCost inputLimit+1) (runAttemptAt 9) := by
  have checked := run_attempt_headers_declaration_parent_root s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal stateGlobal
    padGlobal arena heapArena heapGlobal heapUpper heapBound code budget
  apply reaches_trans s (runAttemptAt 2) (runAttemptAt 3) (runAttemptAt 9) _ _
    (validateHeadersBodyCost inputLimit+1) 0 checked
  intro ready evidence
  obtain ⟨facts,selected⟩ := evidence
  have retained := facts
  obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,countCap,frontier,
    scratchPost,framePost,statePost,padPost,windowPost,tablePost,prefixReady,initialized,atSiReady⟩ := facts
  have counted := run_attempt_header_count_record_reaches s ready si array count input inputLength heap ceiling
    linked value atSi locals domainEq recordAbove recordBefore windowPost
  apply reaches_trans ready (runAttemptAt 3) (runAttemptAt 5) (runAttemptAt 9) _ _ 0 0 counted
  intro next countFacts
  obtain ⟨sameCount,nonzero⟩ := countFacts
  subst next
  obtain ⟨liveHeap,header,root,binding,cell,rootCell,domain,extent,floor⟩ := selected nonzero
  let countedState := setVarHOLFinite (ofString "nh") (.val (.word count)) ready
  have vh : countedState.locals.lookup (ofString "vh")=
      some (.rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))]) := by
    simpa (config := {decide := true}) [countedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using vhLocal
  have nh : countedState.locals.lookup (ofString "nh")=some (.val (.word count)) := by
    simp [countedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have pointerPrefix : HeaderPointerPrefix countedState heap count.toNat :=
    initialized.after_frame ready countedState heap count.toNat rfl (fun _ _=>rfl)
  have selectedRun := run_attempt_selected_parent_root_at9_reaches countedState heap
    (allocationEnd heap (validateHeadersHsSize count)) count header root liveHeap vh nh pointerPrefix nonzero
    binding cell rootCell domain
  apply reaches_mono _ (runAttemptAt 5) (runAttemptAt 9) _ _ 0 0 (Nat.le_refl _) _ selectedRun
  intro final finalFacts
  obtain ⟨parent,same,atParent,parentEq,rootFinal,domainFinal,heapFinal,rest⟩ := finalFacts
  refine ⟨ready,liveHeap,parent,root,retained,nonzero,same,atParent,heapFinal,?_,?_,?_,?_⟩
  · simpa only [parentEq] using rootFinal
  · simpa only [parentEq] using domainFinal
  · simpa only [parentEq] using extent
  · simpa only [parentEq] using floor

#print axioms run_attempt_headers_to_selected_root_reaches
end InitECandidate.Runtime

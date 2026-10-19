import InitECandidate.Runtime.DecodeStepUniformBodyBound
import InitECandidate.Runtime.DecodeStepKindReturnedHeap
import InitECandidate.Runtime.DecodeStepEntryHeapReach
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

private theorem remainingBudget {a b initial remaining : Nat}
    (total : a+b ≤ initial) (spent : initial ≤ remaining+a) : b ≤ remaining := by omega

/-- Every actual returned decoder run has an aligned, capped, monotone heap
frontier and preserves old memory above the scratch ceiling and below the
original heap. All parser, allocator and record-store continuations are original. -/
theorem decode_step_body_returned_heap_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_step) =
      (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      array.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
      ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < array.toNat →
        post.memory watched = s.memory watched := by
  change evaluateHOLFiniteState s (decodeStepAt 0) = _ at run
  have parseMono := decodeStepParseCost_mono length.toNat inputLimit lengthBound
  have actualBudget : decodeStepParseCost length.toNat +
      (decodeStepSlicesCost inputLimit + decodeStepTwoCaseCost inputLimit) ≤ s.clock :=
    (Nat.add_le_add_right parseMono _).trans budget
  have reached := decode_step_entry_heap_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    ((Nat.le_add_right _ _).trans actualBudget)
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 0)
    (decodeStepAt 3) _ _ _ reached (by rw [run])
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 3) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    obtain ⟨kind,pp,payload,atItem,parsedKind,payloadBound,_,ends,span,starts,globals,codeReady,domainReady,_,pointerReady,lengthReady,memoryReady⟩ := facts
    have limit : payload.toNat ≤ inputLimit := payloadBound.trans lengthBound
    have sliceMono := decodeStepSlicesCost_mono payload.toNat inputLimit limit
    have beforeFrame : pp.toNat + payload.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pp.toNat) := by
      rcases inputBeforeFrame with before | ⟨aligned,after⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨aligned,by omega⟩
    have kept := decode_step_kind_returned_heap_contract ready output kind pp payload length scratch frame array pointer length ceiling inputLimit
      pointerReady lengthReady atItem parsedKind span limit limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal)
      (codeReady.trans code) orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      ((Nat.add_le_add_right sliceMono _).trans (remainingBudget actualBudget spent)) ((globals _).trans heap) arrayBound aligned countLimit
      (by intro address lower upper; rw [domainReady]; exact heapArena address lower upper)
      beforeFrame (by omega) arrayAbove limitCap value tailRun
    obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memoryPost⟩ := kept
    have globals := agreement.2.2.2.1
    have finalMemory := agreement.2.2.1
    rw [run,tailRun] at globals finalMemory
    change post.globals = output.globals at globals
    change post.memory = output.memory at finalMemory
    refine ⟨nextHeap,?_,growth,capped,finishAligned,?_⟩
    · rw [globals]; exact heapPost
    · intro watched above before
      rw [finalMemory]
      exact (memoryPost watched above before).trans (memoryReady watched above)

#print axioms decode_step_body_returned_heap_contract
end InitECandidate.Runtime

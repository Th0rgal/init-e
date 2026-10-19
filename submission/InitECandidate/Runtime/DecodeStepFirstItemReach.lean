import InitECandidate.Runtime.DecodeStepArityDispatch
import InitECandidate.Runtime.RlpItemBodyRuntimeContract
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.DecodeStepCompactCall
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepFirstItemArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.const 0,.const 16]]),
   .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.const 0,.const 16],.const 8])]

def decodeStepFirstItemTail : ProgHOL 64 :=
  match decodeStepTwoCase with | .decCall _ _ _ _ tail => tail | _ => .skip

theorem source_decode_step_first_item : decodeStepTwoCase =
    .decCall (ofString "pi") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
      decodeStepFirstItemArguments decodeStepFirstItemTail := by
  simp only [decodeStepTwoCase,decodeStepAt,decodeStepFirstItemArguments,decodeStepFirstItemTail,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The first actual slice is parsed into the actual two-item node continuation,
with its bounded payload and restored workspace. -/
theorem decode_step_first_item_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 0 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat*((2*length.toNat+1)*15+19)+92633 ≤ s.clock) :
    Reaches s decodeStepTwoCase
      (fun next => ∃ kind payloadPointer payload consumed : BitVec 64,
        next.locals.lookup (ofString "pi") = some
          (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) ∧
        pointer.toNat ≤ payloadPointer.toNat ∧
        payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
        payloadPointer.toNat + payload.toNat < 2^64 ∧ payload.toNat ≤ length.toNat ∧
        next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        next.globals.lookup (ofString "heap_ptr") = s.globals.lookup (ofString "heap_ptr") ∧
        next.code = s.code ∧ next.memaddrs = s.memaddrs ∧
        next.locals = s.locals.update (ofString "pi",
          .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]))
      (length.toNat*((2*length.toNat+1)*15+19)+92633) decodeStepFirstItemTail := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) decodeStepFirstItemArguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [decodeStepFirstItemArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
      show s.memaddrs array from by simpa using slice.pointerDomain,
      show s.memory array = .word pointer from by simpa using slice.pointerCell,
      show s.memaddrs (array + 8#64) from by simpa using slice.lengthDomain,
      show s.memory (array + 8#64) = .word length from by simpa using slice.lengthCell]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit p n
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock - 1; omega)
  rw [source_decode_step_first_item]
  apply bounded_decCall_reaches s (ofString "pi") (ofString "rlp_item") (.comb [.one,.one,.one,.one])
    (.comb [.one,.one,.one,.one]) _ _ _ _ (rlpHeaderCallee pointer length)
    (length.toNat*((2*length.toNat+1)*15+19)+92632) _ args lookup (by omega) bounded
  intro value post run shapes
  obtain ⟨kind,pp,payload,consumed,rfl,starts,ends,span,small,scratchPost,framePost,heapPost⟩ :=
    rlpItem_body_returned_runtime_contract entry post pointer length scratch frame ceiling inputLimit p n
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change _ ≤ s.clock - 1; omega) value run
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [run] at metadata
  exact ⟨kind,pp,payload,consumed,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
    starts,ends,span,small,scratchPost,framePost,heapPost,metadata.1,metadata.2.1,rfl⟩

theorem source_decode_step_first_item_guard : decodeStepFirstItemTail =
    .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "pi"))) (.const 0))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) decodeStepCompactCall := by
  simp only [decodeStepFirstItemTail,decodeStepTwoCase,decodeStepAt,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A string-valued compact path proceeds to the actual compact decoder in the
same state; the check itself has zero source-clock cost. -/
theorem evaluate_decode_step_first_item_string {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length consumed : BitVec 64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word (0#64)),.val (.word pointer),.val (.word length),.val (.word consumed)])) :
    evaluateHOLFiniteState s decodeStepFirstItemTail = evaluateHOLFiniteState s decodeStepCompactCall := by
  rw [source_decode_step_first_item_guard,evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_skip]

#print axioms source_decode_step_first_item_guard
#print axioms evaluate_decode_step_first_item_string
#print axioms source_decode_step_first_item
#print axioms decode_step_first_item_reaches
end InitECandidate.Runtime

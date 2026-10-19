import InitECandidate.Runtime.DecodeStepFirstItemReach
import InitECandidate.Runtime.DecodeStepLeafValueUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepLeafItemArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.const 1,.const 16]]),
   .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.const 1,.const 16],.const 8])]

theorem source_decode_step_leaf_branch : decodeStepLeafBranch =
    .decCall (ofString "vi") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
      decodeStepLeafItemArguments decodeStepLeafValueContinuation := by
  simp only [decodeStepLeafBranch,decodeStepLeafItemArguments,decodeStepLeafValueContinuation,
    decodeStepCompactContinuation,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual second-slice parser, value-type check and leaf construction have
an explicit all-outcome bound. Slice arguments come from the real table cells. -/
theorem runBounded_decode_step_leaf_branch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat*((2*length.toNat+1)*15+19)+92637 ≤ s.clock) :
    RunBounded s decodeStepLeafBranch (length.toNat*((2*length.toNat+1)*15+19)+92637) := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) decodeStepLeafItemArguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [decodeStepLeafItemArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
      show s.memaddrs (array + 16#64) from by simpa using slice.pointerDomain,
      show s.memory (array + 16#64) = .word pointer from by simpa using slice.pointerCell,
      show s.memaddrs (array + 24#64) from by simpa [BitVec.add_assoc] using slice.lengthDomain,
      show s.memory (array + 24#64) = .word length from by simpa [BitVec.add_assoc] using slice.lengthCell]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit p n
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock - 1; omega)
  rw [source_decode_step_leaf_branch]
  have whole := RunBounded.decCall (bodyCost := length.toNat*((2*length.toNat+1)*15+19)+92632) (tailCost := 4)
    (name := ofString "vi") (shape := .comb [.one,.one,.one,.one]) (continuation := decodeStepLeafValueContinuation)
    args (by omega) (by
      intro body callee shape found
      rw [lookup] at found
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl,rfl⟩ := found
      refine ⟨bounded,?_⟩
      intro value post run ticks
      have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
      change evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item) = _ at run
      rw [run] at metadata
      exact RunBounded.ofProg decode_step_leaf_value_uniform_bounded (metadata.1.trans code) ticks)
  exact whole.weaken (by omega)

#print axioms source_decode_step_leaf_branch
#print axioms runBounded_decode_step_leaf_branch
end InitECandidate.Runtime

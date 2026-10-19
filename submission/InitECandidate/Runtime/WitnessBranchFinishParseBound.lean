import InitECandidate.Runtime.WitnessBranchFinishTailBound
import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RunBoundedReaches
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessBranchFinishCost (n : Nat) : Nat := n*((2*n+1)*15+19)+92634

/-- The actual final-value parser plus occupancy checks/cache/pop tail is
bounded on every outcome, including parser exceptions and failed stores. -/
theorem runBounded_witness_branch_finish_parse {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr2") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock) :
    RunBounded s (witnessBranchFinishAt 1) (witnessBranchFinishCost length.toNat) := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16]]),
       .load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16],.const 8])] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,wordOpHOL,wordOp,panOpHOL,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    have factor : (16 : BitVec 64)*16#64 = 256#64 := by decide
    have pd : s.memaddrs (array+256#64) := by simpa only [factor] using slice.pointerDomain
    have pc : s.memory (array+256#64) = .word pointer := by simpa only [factor] using slice.pointerCell
    have ld : s.memaddrs (array+264#64) := by
      simpa only [factor,BitVec.add_assoc,show 256#64+8#64 = 264#64 from by decide] using slice.lengthDomain
    have lc : s.memory (array+264#64) = .word length := by
      simpa only [factor,BitVec.add_assoc,show 256#64+8#64 = 264#64 from by decide] using slice.lengthCell
    rw [if_pos pd,pc,if_pos ld,lc]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have body := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit p n inputRange
    lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock-1; unfold witnessBranchFinishCost at budget; omega)
  have reached : Reaches s (witnessBranchFinishAt 1) (fun ready => ready.code = originalRuntimeCode)
      (length.toNat*((2*length.toNat+1)*15+19)+92633) (witnessBranchFinishAt 2) := by
    rw [source_witness_branch_finish_parse]
    apply bounded_decCall_reaches s (ofString "bv") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _ _ _ (rlpHeaderCallee pointer length)
      (length.toNat*((2*length.toNat+1)*15+19)+92632) _ args lookup
      (by unfold witnessBranchFinishCost at budget; omega) body
    intro value post run shapes
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
    rw [run] at metadata
    exact metadata.1.trans code
  have closed := RunBounded.ofReaches (tailCost := 1) (by unfold witnessBranchFinishCost at budget; omega) reached
    (fun ready installed ticks => RunBounded.ofProg witness_branch_finish_tail_bounded installed ticks)
  simpa [witnessBranchFinishCost,Nat.add_assoc] using closed

#print axioms runBounded_witness_branch_finish_parse
end InitECandidate.Runtime

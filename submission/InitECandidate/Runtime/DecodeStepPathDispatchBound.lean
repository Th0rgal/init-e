import InitECandidate.Runtime.DecodeStepLeafBranchUniformBound
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
import InitECandidate.Runtime.TerminalTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_leaf_branch_terminal : terminalTail decodeStepLeafBranch = true := by
  rw [source_decode_step_leaf_branch,source_decodeStep_leaf_value_continuation,
    source_decodeStep_leaf_construction,source_decodeStep_leaf_stores]
  rfl

/-- The real leaf path returns or rejects; it cannot fall through to allocate an
extension record after finishing its own constructor. -/
theorem evaluate_decode_step_leaf_dispatch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer count leaf : BitVec 64) (nonzero : leaf ≠ 0)
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word pointer),.val (.word count),.val (.word leaf)])) :
    evaluateHOLFiniteState s decodeStepCompactContinuation = evaluateHOLFiniteState s decodeStepLeafBranch := by
  rw [source_decodeStep_path_dispatch,evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atPath,Compiler.Encoders.Asm.wordCmpHOL,
    show leaf ≠ 0#64 from nonzero]
  cases branchRun : evaluateHOLFiniteState s decodeStepLeafBranch with
  | mk result post =>
    cases result with
    | none =>
      have terminal := evaluate_terminalTail decodeStepLeafBranch decode_step_leaf_branch_terminal s
      rw [branchRun] at terminal
      exact False.elim (terminal rfl)
    | some result => rfl

/-- Both actual compact-result branches have a common bound; allocation and
memory failures are included and no assumptions on nibble count are needed here. -/
theorem runBounded_decode_step_compact_continuation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame nibs count leaf : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat*((2*length.toNat+1)*15+19)+92637 ≤ s.clock)
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)])) :
    RunBounded s decodeStepCompactContinuation (length.toNat*((2*length.toNat+1)*15+19)+92637) := by
  by_cases zero : leaf = 0
  · subst leaf
    unfold RunBounded
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath]
    exact (runBounded_decode_step_extension_suffix s scratch frame scratchGlobal frameGlobal code (by omega)).weaken (by omega)
  · unfold RunBounded
    rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath]
    exact runBounded_decode_step_leaf_branch s array pointer length scratch frame ceiling inputLimit atArray slice
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms decode_step_leaf_branch_terminal
#print axioms evaluate_decode_step_leaf_dispatch
#print axioms runBounded_decode_step_compact_continuation
end InitECandidate.Runtime

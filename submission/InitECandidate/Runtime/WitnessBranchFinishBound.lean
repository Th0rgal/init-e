import InitECandidate.Runtime.WitnessBranchFinishParseBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_witness_branch_finish {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock) :
    RunBounded s (witnessBranchFinishAt 0) (witnessBranchFinishCost length.toNat) := by
  rw [source_witness_branch_finish_entry]
  apply RunBounded.dec
  intro value initialized
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "top"),.const 24])) = some (.val (.word array)) := by
    simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,arrayReadable,arrayCell]
  rw [evalArray] at initialized
  cases initialized
  let entered := setVarHOLFinite (ofString "arr2") (.val (.word array)) s
  exact runBounded_witness_branch_finish_parse entered array pointer length scratch frame ceiling inputLimit
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (slice.after_frame s entered array 16 pointer length rfl rfl rfl)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms runBounded_witness_branch_finish
end InitECandidate.Runtime

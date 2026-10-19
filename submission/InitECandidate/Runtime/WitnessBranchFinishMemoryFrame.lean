import InitECandidate.Runtime.WitnessBranchFinishParseMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_branch_finish_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 0) = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  rw [source_witness_branch_finish_entry] at run
  obtain ⟨value,output,initialized,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post (ofString "arr2") .one _ (witnessBranchFinishAt 1) run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "top"),.const 24])) = some (.val (.word array)) := by
    simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,arrayReadable,arrayCell]
  rw [evalArray] at initialized
  cases initialized
  let entered := setVarHOLFinite (ofString "arr2") (.val (.word array)) s
  have localFrame (name : MlS) (different : name ≠ ofString "arr2") :
      entered.locals.lookup name = s.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have facts := witness_branch_finish_parse_normal_memory_frame entered output
    array pointer length scratch frame heap ceiling inputLimit
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((localFrame _ (by decide)).trans atBr) heapBound (slice.after_frame s entered array 16 pointer length rfl rfl rfl)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  rw [postEq]
  exact facts

#print axioms witness_branch_finish_normal_memory_frame
end InitECandidate.Runtime

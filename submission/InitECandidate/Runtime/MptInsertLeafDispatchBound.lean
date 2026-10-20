import InitECandidate.Runtime.MptInsertLeafCallBound
import InitECandidate.Runtime.MptInsertBranchValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertLeafDispatch : ProgHOL 64 :=
 match mptInsertKindDispatch with | .seq _ (.seq _ (.ite _ leaf _))=>leaf | _=>.skip

theorem source_mptInsert_leaf_dispatch : mptInsertLeafDispatch=
 .call (some (some (.local,ofString "r"),none)) (ofString "_insert_into_leaf")
  [.var .local (ofString "node"),.op .add [.var .local (ofString "key"),.var .local (ofString "level")],
   .op .sub [.var .local (ofString "klen"),.var .local (ofString "level")],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")] := by
 simp only [mptInsertLeafDispatch,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
  Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- The actual leaf branch in the insertion loop inherits the indexed-key
ceiling from level<=klen<=18, including its real key-offset subtraction. -/
theorem mpt_insert_leaf_dispatch_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node key length level valuePointer valueLength : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 2^64+201≤s.clock) :
 RunBounded s mptInsertLeafDispatch (2^64+201) := by
 rw [source_mptInsert_leaf_dispatch]
 apply mpt_insert_leaf_call_bounded s _ _ node (key+level) (length-level) valuePointer valueLength
 · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNode,atKey,atLength,atLevel,atValue,atValueLength,
    wordOpHOL,wordOp,valueIsWord,valueWord]
 · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)]
   omega
 · exact code
 · exact budget

#print axioms source_mptInsert_leaf_dispatch
#print axioms mpt_insert_leaf_dispatch_bounded
end InitECandidate.Runtime

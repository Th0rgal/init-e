import InitECandidate.Runtime.MptInsertLeafDispatchBound
import InitECandidate.Runtime.MptInsertExtensionDispatchBound
import InitECandidate.Runtime.RunBoundedIte
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertKindChoice : ProgHOL 64 :=
 match mptInsertKindDispatch with | .seq _ (.seq _ choice)=>choice | _=>.skip

def mptInsertBranchDispatch : ProgHOL 64 :=
 match mptInsertKindChoice with | .ite _ _ (.ite _ _ branch)=>branch | _=>.skip

theorem source_mptInsert_kind_choice : mptInsertKindChoice=
 .ite (.cmp .equal (.var .local (ofString "k")) (.const 1)) mptInsertLeafDispatch
  (.ite (.cmp .equal (.var .local (ofString "k")) (.const 2)) mptInsertExtensionDispatch mptInsertBranchDispatch) := by
 simp only [mptInsertKindChoice,mptInsertBranchDispatch,mptInsertLeafDispatch,mptInsertExtensionDispatch,
  mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem mpt_insert_branch_dispatch_bounded : ProgBounded mptInsertBranchDispatch 0 := by
 apply ProgBounded.straight
 simp only [mptInsertBranchDispatch,mptInsertKindChoice,mptInsertKindDispatch,mptInsertLoopStep,
  sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- The actual leaf/extension/branch choice has one uniform indexed-key
iteration budget. No trie validity, memory readability or allocation-room
premise is used by this runtime theorem. -/
theorem mpt_insert_kind_choice_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node key length level valuePointer valueLength : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 2^64+201≤s.clock) :
 RunBounded s mptInsertKindChoice (2^64+201) := by
 rw [source_mptInsert_kind_choice]
 apply RunBounded.ite
 · exact mpt_insert_leaf_dispatch_bounded s node key length level valuePointer valueLength atNode atKey atLength
    atLevel atValue atValueLength inside short code budget
 · apply RunBounded.ite
   · exact RunBounded.weaken (mpt_insert_extension_dispatch_bounded s code (by omega)) (by omega)
   · exact RunBounded.weaken (mpt_insert_branch_dispatch_bounded s code (by omega)) (by omega)

#print axioms source_mptInsert_kind_choice
#print axioms mpt_insert_branch_dispatch_bounded
#print axioms mpt_insert_kind_choice_bounded
end InitECandidate.Runtime

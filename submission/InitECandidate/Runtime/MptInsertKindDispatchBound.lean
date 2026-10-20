import InitECandidate.Runtime.MptInsertChoiceBound
import InitECandidate.Runtime.NodeInvalidateRegistry
import InitECandidate.Runtime.OriginalNodeInvalidateCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertKindGuard : ProgHOL 64 :=
 match mptInsertKindDispatch with | .seq guard _=>guard | _=>.skip

def mptInsertInvalidate : ProgHOL 64 :=
 match mptInsertKindDispatch with | .seq _ (.seq invalidate _)=>invalidate | _=>.skip

theorem source_mptInsert_kind_dispatch : mptInsertKindDispatch=
 .seq mptInsertKindGuard (.seq mptInsertInvalidate mptInsertKindChoice) := by
 simp only [mptInsertKindGuard,mptInsertInvalidate,mptInsertKindChoice,mptInsertKindDispatch,mptInsertLoopStep,
  sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem source_mptInsert_kind_guard : mptInsertKindGuard=
 .ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
  (.call (some (none,none)) (ofString "mpt_fail") [.const 2]) .skip := by
 simp only [mptInsertKindGuard,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
  Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem source_mptInsert_invalidate : mptInsertInvalidate=
 .call (some (none,none)) (ofString "node_invalidate") [.var .local (ofString "node")] := by
 simp only [mptInsertInvalidate,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
  Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem node_invalidate_fun_bounded : FunBounded (ofString "node_invalidate") 0 :=
 ⟨_,_,_,originalRuntimeCode_nodeInvalidate_lookup,
  ProgBounded.straight _ (by rw [source_nodeInvalidate_body];rfl)⟩

theorem mpt_insert_kind_guard_bounded : ProgBounded mptInsertKindGuard 1 := by
 rw [source_mptInsert_kind_guard]
 apply ProgBounded.ite
 · exact ProgBounded.call mpt_fail_fun_bounded _ _
 · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)

theorem mpt_insert_invalidate_bounded : ProgBounded mptInsertInvalidate 1 := by
 rw [source_mptInsert_invalidate]
 exact ProgBounded.call node_invalidate_fun_bounded _ _

/-- The original non-null dispatch includes its real invalid-kind guard and
cache invalidation call. Their normal outcomes restore caller locals, so the
indexed remaining-length premise reaches the actual leaf call unchanged. -/
theorem mpt_insert_kind_dispatch_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node key length level valuePointer valueLength : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 2^64+203≤s.clock) :
 RunBounded s mptInsertKindDispatch (2^64+203) := by
 rw [source_mptInsert_kind_dispatch]
 have bounded : RunBounded s (.seq mptInsertKindGuard (.seq mptInsertInvalidate mptInsertKindChoice))
  (1+(1+(2^64+201))) := by
  refine RunBounded.seq (mpt_insert_kind_guard_bounded s code (by omega)) (by omega) ?_
  intro guarded guardRun guardCode guardBudget
  have guardLocals : guarded.locals=s.locals := by
   rw [source_mptInsert_kind_guard] at guardRun
   exact evaluate_discard_guard_normal_locals s guarded _ _ _ guardRun
  refine RunBounded.seq (mpt_insert_invalidate_bounded guarded (guardCode.trans code) (by omega)) guardBudget ?_
  intro invalidated invalidateRun invalidateCode invalidateBudget
  have callLocals : invalidated.locals=guarded.locals := by
   rw [source_mptInsert_invalidate] at invalidateRun
   have kept:=evaluate_discard_call_success_locals guarded (ofString "node_invalidate") _ (by rw [invalidateRun])
   rw [invalidateRun] at kept
   exact kept
  have locals : invalidated.locals=s.locals:=callLocals.trans guardLocals
  exact mpt_insert_kind_choice_bounded invalidated node key length level valuePointer valueLength
   (by rw [locals];exact atNode) (by rw [locals];exact atKey) (by rw [locals];exact atLength)
   (by rw [locals];exact atLevel) (by rw [locals];exact atValue) (by rw [locals];exact atValueLength)
   inside short (invalidateCode.trans (guardCode.trans code)) invalidateBudget
 exact bounded.weaken (by omega)

#print axioms node_invalidate_fun_bounded
#print axioms mpt_insert_kind_dispatch_bounded
end InitECandidate.Runtime

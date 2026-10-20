import InitECandidate.Runtime.MptInsertTerminalGo
import InitECandidate.Runtime.MptInsertBranchDescent
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A continuing normal node-kind choice cannot have taken the leaf call. -/
theorem mpt_insert_kind_choice_running {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (kind : BitVec 64) (atKind : s.locals.lookup (ofString "k")=some (.val (.word kind)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertKindChoice=(none,post)) :
 (kind=2#64 ∧evaluateHOLFiniteState s mptInsertExtensionDispatch=(none,post)) ∨
 (kind≠1#64 ∧kind≠2#64 ∧evaluateHOLFiniteState s mptInsertBranchDispatch=(none,post)) := by
 have cmp (constant : BitVec 64) : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "k")) (.const constant))=
  some (.val (.word (if kind=constant then 1#64 else 0#64))) := by
  simp [evalHOLExact,atKind,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_mptInsert_kind_choice,evaluateHOLFiniteState_ite,cmp] at run
 by_cases leaf : kind=1#64
 · have leafRaw : kind=1:=leaf
   simp only [if_pos leafRaw,show (1#64)≠0 from by decide,if_false] at run
   exact False.elim (running (mpt_insert_leaf_normal_stopped s post zero run))
 · have leafRaw : kind≠1:=leaf
   simp only [if_neg leafRaw,if_pos rfl] at run
   change evaluateHOLFiniteState s (.ite _ mptInsertExtensionDispatch mptInsertBranchDispatch)=(none,post) at run
   rw [evaluateHOLFiniteState_ite,cmp] at run
   by_cases extension : kind=2#64
   · have extensionRaw : kind=2:=extension
     simp only [if_pos extensionRaw,show (1#64)≠0 from by decide,if_false] at run
     exact Or.inl ⟨extension,run⟩
   · have extensionRaw : kind≠2:=extension
     simp only [if_neg extensionRaw,if_pos rfl] at run
     exact Or.inr ⟨leaf,extension,run⟩

theorem source_mptInsert_branch_dispatch : mptInsertBranchDispatch=
 .ite (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))
  mptInsertBranchValue mptInsertBranchDescent := by
 simp only [mptInsertBranchDispatch,mptInsertKindChoice,mptInsertBranchValue,mptInsertBranchDescent,
  mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- A continuing normal branch path must descend at a strictly smaller level
than klen. The completed-key value update leaves go zero. -/
theorem mpt_insert_branch_dispatch_running {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (level length : BitVec 64)
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (inside : level.toNat≤length.toNat)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertBranchDispatch=(none,post)) :
 level.toNat<length.toNat ∧evaluateHOLFiniteState s mptInsertBranchDescent=(none,post) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))=
  some (.val (.word (if level=length then 1#64 else 0#64))) := by
  simp [evalHOLExact,atLevel,atLength,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_mptInsert_branch_dispatch,evaluateHOLFiniteState_ite,cmp] at run
 by_cases terminal : level=length
 · simp only [if_pos terminal] at run
   exact False.elim (running (mpt_insert_branch_value_normal_stopped s post zero run))
 · simp only [if_neg terminal] at run
   have different : level.toNat≠length.toNat:=fun same=>terminal (BitVec.eq_of_toNat_eq same)
   exact ⟨by omega,run⟩

#print axioms mpt_insert_kind_choice_running
#print axioms mpt_insert_branch_dispatch_running
end InitECandidate.Runtime

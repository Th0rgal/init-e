import InitECandidate.Runtime.WitnessUnwindPrefixFrame
import InitECandidate.Runtime.WitnessBranchEntryNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Exact actual hash declaration/store continuation. The final hash local alone
is restored; all other final locals are the stage branch's actual output. -/
theorem witness_unwind_nonempty_normal_prefix {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindNonempty=(none,post)) :
    ∃ next output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState next (.ite (.cmp .equal (.load .one (.op .add
        [.var .local (ofString "top"),.const 8])) (.const 1)) witnessUnwindExtension witnessUnwindBranch)=(none,output) ∧
      next.locals=(setVarHOLFinite (ofString "hash") (.val (.word hash)) s).locals ∧
      next.globals=s.globals ∧ next.code=s.code ∧ next.memaddrs=s.memaddrs ∧ next.be=s.be ∧ next.clock=s.clock ∧
      (∀ watched : BitVec 64, result=0 ∨ watched ≠ result+24 → next.memory watched=s.memory watched) ∧
      post.memory=output.memory ∧ post.globals=output.globals ∧
      (∀ name, name ≠ ofString "hash" → post.locals.lookup name=output.locals.lookup name) := by
  rw [source_witness_unwind_nonempty] at run
  obtain ⟨hashValue,output,initialized,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post _ _ _ _ run
  have hashValueEq : hashValue = .val (.word hash) := by
    have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 80])) = some (.val (.word hash)) := by
      simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,hashReadable,hashCell]
    exact Option.some.inj (initialized.symm.trans evaluated)
  subst hashValue
  let entered := setVarHOLFinite (ofString "hash") (.val (.word hash)) s
  obtain ⟨next,hashRun,tailRun⟩ := witness_extension_sequence_normal_parts entered output _ _ bodyRun
  have atHash : entered.locals.lookup (ofString "hash")=some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredResult : entered.locals.lookup (ofString "result")=some (.val (.word result)) := by
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atResult
  have frames := witness_unwind_hash_store_frame entered result hash atHash enteredResult code
  have metadata := evaluateHOLFiniteState_metadata entered witnessUnwindHashStore
  have bounded := witness_unwind_hash_store_bounded entered code (Nat.zero_le _)
  rw [hashRun] at frames metadata bounded
  refine ⟨next,output,tailRun,frames.1,frames.2.1,metadata.1,metadata.2.1,metadata.2.2.1,?_,frames.2.2,?_,?_,?_⟩
  · change next.clock=s.clock
    change s.clock ≤ next.clock+0 ∧ next.clock≤s.clock ∧ _ at bounded
    omega
  · rw [postEq]
  · rw [postEq]
  · intro name different
    rw [postEq]
    exact restore_other_local _ _ _ _ different
#print axioms witness_unwind_nonempty_normal_prefix
end InitECandidate.Runtime

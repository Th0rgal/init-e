import InitECandidate.Runtime.WitnessUnwindPrefixFrame
import InitECandidate.Runtime.WitnessExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem runBounded_witness_unwind_extension_nonempty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top result hash : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode) (budget : 5 ≤ s.clock) :
    RunBounded s witnessUnwindNonempty 5 := by
  rw [source_witness_unwind_nonempty]
  apply RunBounded.decWord s (ofString "hash") _ hash
  · simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,hashReadable,hashCell]
  let entered := setVarHOLFinite (ofString "hash") (.val (.word hash)) s
  have other (name : MlS) (different : name ≠ ofString "hash") : entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atHash : entered.locals.lookup (ofString "hash")=some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTopEntered := (other _ (by decide)).trans atTop
  have atResultEntered := (other _ (by decide)).trans atResult
  have enteredBudget : 5 ≤ entered.clock := budget
  have whole := RunBounded.seq (tail := .ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))
      witnessUnwindExtension witnessUnwindBranch) (b := 5)
    (RunBounded.ofProg (state := entered) witness_unwind_hash_store_bounded code (by omega))
    (by simpa only [Nat.zero_add] using enteredBudget) (by
      intro next normal nextCode ticks
      have frames := witness_unwind_hash_store_frame entered result hash atHash atResultEntered code
      have metadata := evaluateHOLFiniteState_metadata entered witnessUnwindHashStore
      rw [normal] at frames metadata
      have nextTop : next.locals.lookup (ofString "top")=some (.val (.word top)) := by
        rw [frames.1]; exact atTopEntered
      have stageNat : (top+8#64).toNat=top.toNat+8 := by
        rw [BitVec.toNat_add]
        change (top.toNat+8)%2^64=top.toNat+8
        exact Nat.mod_eq_of_lt (by omega)
      have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
        rw [BitVec.toNat_add]
        change (result.toNat+24)%2^64=result.toNat+24
        exact Nat.mod_eq_of_lt (by omega)
      have stageKept : next.memory (top+8#64)=s.memory (top+8#64) := by
        apply frames.2.2
        rcases resultAfterRecord with zero | lower
        · exact Or.inl zero
        · apply Or.inr
          intro same
          have equal := congrArg BitVec.toNat same
          rw [stageNat,resultNat] at equal
          omega
      have condition : @evalHOLExact 64 F _ next.toExact (fun a => Classical.propDecidable (next.memaddrs a))
          (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))=
          some (.val (.word (1#64))) := by
        simp [evalHOLExact,evalListHOLExact,nextTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
          memLoadHOLExact,
          show next.memaddrs (top+8#64) from by rw [metadata.2.1]; exact stageReadable,
          stageKept,stageCell,Compiler.Encoders.Asm.wordCmpHOL]
      unfold RunBounded
      rw [evaluateHOLFiniteState_ite,condition]
      change RunBounded next witnessUnwindExtension 5
      exact runBounded_witness_extension next (metadata.1.trans code) ticks)
  simpa using whole

#print axioms runBounded_witness_unwind_extension_nonempty
end InitECandidate.Runtime

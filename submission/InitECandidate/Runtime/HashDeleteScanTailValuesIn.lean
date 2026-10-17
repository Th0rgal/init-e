import InitECandidate.Runtime.HashDeleteLinkedLoopLocalSupported
import InitECandidate.Runtime.HashDeleteFinalTailEntriesValuesIn
import InitECandidate.Runtime.HashDeleteLoopValuesIn
import InitECandidate.Runtime.HashDeleteLinkedLoopMetadataSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scan and final suffix return with live linkage for the
smaller table, within 55 clocks per slot. -/
theorem evaluate_hashDelete_scan_tail_values_in {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 55 ≤ state.clock)
    (deletedBound : deletedPosition.toNat < items.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition))) :
    ∃ post, evaluateHOLFiniteState state (.seq hashDeleteLoop hashDeleteFinalTail) =
      (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨scanned,scanRun,exitValid,cost,remaining,tFrame⟩ := evaluate_hashDelete_linked_loop_local_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
    (ofString "t") (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨checked,checkedRun,_,_,_,deletedFrame⟩ := evaluate_hashDelete_linked_loop_local_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
    (ofString "deleted_pos") (by decide) (by decide) (by decide) (by decide) (by decide)
  have same : scanned = checked := congrArg Prod.snd (scanRun.symm.trans checkedRun)
  have saved : scanned.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)) := by
    rw [same,deletedFrame]
    exact deletedLocal
  obtain ⟨metaPost,metaRun,_,_,_,metaGlobals,metaCode,metaDomain,metaEndian⟩ := evaluate_hashDelete_linked_loop_metadata_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
  have metaSame : scanned = metaPost := congrArg Prod.snd (scanRun.symm.trans metaRun)
  obtain ⟨valuePost,valueRun,_,valueRegistered,_,_⟩ := evaluate_hashDelete_loop_values_in
    keyLength table keys stride capacity used values order orderPos items empty bits state valid.base supported targets registered budget
  have valueSame : scanned = valuePost := congrArg Prod.snd (scanRun.symm.trans valueRun)
  have scannedRegistered : HashTableValuesIn table targets scanned := by rw [valueSame]; exact valueRegistered
  obtain ⟨base,hole,holeLocal,linked⟩ := exitValid
  obtain ⟨actualHole,index,holeInside,_,actualLocal,_,_⟩ := base.indices
  have holeSame : actualHole = hole := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualLocal.symm.trans holeLocal
  have inside : hole.toNat < capacity.toNat := by simpa [holeSame] using holeInside
  obtain ⟨post,tail,postRegistered,ticks,globals,code,domain,endian⟩ := evaluate_hashDelete_final_tail_entries_values_in scanned
    keyLength table keys stride capacity used values order orderPos items hole deletedPosition bits base.arrays targets scannedRegistered inside deletedBound base.ordered
    (tFrame.trans tableLocal) base.orderLocal base.reverseLocal saved base.usedLocal holeLocal
  have scannedGlobals : scanned.globals = state.globals := by rw [metaSame]; exact metaGlobals
  have scannedCode : scanned.code = state.code := by rw [metaSame]; exact metaCode
  have scannedDomain : scanned.memaddrs = state.memaddrs := by rw [metaSame]; exact metaDomain
  have scannedEndian : scanned.be = state.be := by rw [metaSame]; exact metaEndian
  refine ⟨post,?_,postRegistered,by omega,by omega,globals.trans scannedGlobals,code.trans scannedCode,domain.trans scannedDomain,endian.trans scannedEndian⟩
  rw [evaluateHOLFiniteState_seq_line780,scanRun]
  exact tail

#print axioms evaluate_hashDelete_scan_tail_values_in
end InitECandidate.Runtime

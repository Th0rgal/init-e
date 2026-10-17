import InitECandidate.Runtime.HashDeleteLinkedLoopLocal32
import InitECandidate.Runtime.HashDeleteFinalTailMetadataEntries32
import InitECandidate.Runtime.HashDeleteLinkedLoopMetadata32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scan and final suffix return with live linkage for the
smaller table, within 35 clocks per slot. -/
theorem evaluate_hashDelete_scan_tail_metadata32 {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (budget : capacity.toNat * 35 ≤ state.clock)
    (deletedBound : deletedPosition.toNat < items.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition))) :
    ∃ post, evaluateHOLFiniteState state (.seq hashDeleteLoop hashDeleteFinalTail) =
      (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨scanned,scanRun,exitValid,cost,remaining,tFrame⟩ := evaluate_hashDelete_linked_loop_local32
    table keys stride capacity used values order orderPos items empty deletedPosition bits state valid budget
    (ofString "t") (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨checked,checkedRun,_,_,_,deletedFrame⟩ := evaluate_hashDelete_linked_loop_local32
    table keys stride capacity used values order orderPos items empty deletedPosition bits state valid budget
    (ofString "deleted_pos") (by decide) (by decide) (by decide) (by decide) (by decide)
  have same : scanned = checked := congrArg Prod.snd (scanRun.symm.trans checkedRun)
  have saved : scanned.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)) := by
    rw [same,deletedFrame]
    exact deletedLocal
  obtain ⟨metaPost,metaRun,_,_,_,metaGlobals,metaCode,metaDomain,metaEndian⟩ := evaluate_hashDelete_linked_loop_metadata32
    table keys stride capacity used values order orderPos items empty deletedPosition bits state valid budget
  have metaSame : scanned = metaPost := congrArg Prod.snd (scanRun.symm.trans metaRun)
  obtain ⟨base,hole,holeLocal,linked⟩ := exitValid
  obtain ⟨actualHole,index,holeInside,_,actualLocal,_,_⟩ := base.indices
  have holeSame : actualHole = hole := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualLocal.symm.trans holeLocal
  have inside : hole.toNat < capacity.toNat := by simpa [holeSame] using holeInside
  obtain ⟨post,tail,ticks,globals,code,domain,endian⟩ := evaluate_hashDelete_final_tail_metadata_entries32 scanned
    table keys stride capacity used values order orderPos items hole deletedPosition bits base.arrays inside deletedBound base.ordered
    (tFrame.trans tableLocal) base.orderLocal base.reverseLocal saved base.usedLocal holeLocal
  have scannedGlobals : scanned.globals = state.globals := by rw [metaSame]; exact metaGlobals
  have scannedCode : scanned.code = state.code := by rw [metaSame]; exact metaCode
  have scannedDomain : scanned.memaddrs = state.memaddrs := by rw [metaSame]; exact metaDomain
  have scannedEndian : scanned.be = state.be := by rw [metaSame]; exact metaEndian
  refine ⟨post,?_,by omega,by omega,globals.trans scannedGlobals,code.trans scannedCode,domain.trans scannedDomain,endian.trans scannedEndian⟩
  rw [evaluateHOLFiniteState_seq_line780,scanRun]
  exact tail

#print axioms evaluate_hashDelete_scan_tail_metadata32
end InitECandidate.Runtime

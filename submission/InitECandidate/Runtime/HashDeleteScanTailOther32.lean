import InitECandidate.Runtime.HashDeleteScanTailMetadata32
import InitECandidate.Runtime.HashDeleteLinkedLoopOther32
import InitECandidate.Runtime.HashDeleteFinalTailDisjoint32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original scan and final bookkeeping preserve a disjoint ready table. -/
theorem evaluate_hashDelete_scan_tail_other32 {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (budget : capacity.toNat * 35 ≤ state.clock)
    (deletedBound : deletedPosition.toNat < items.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.seq hashDeleteLoop hashDeleteFinalTail) =
      (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
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
  obtain ⟨metaPost,metaRun,_,metaReady,_,_,metaGlobals,metaCode,metaDomain,metaEndian⟩ := evaluate_hashDelete_linked_loop_other32
    table keys stride capacity used values order orderPos items empty deletedPosition bits state valid
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits ready separated budget
  have metaSame : scanned = metaPost := congrArg Prod.snd (scanRun.symm.trans metaRun)
  obtain ⟨base,hole,holeLocal,linked⟩ := exitValid
  obtain ⟨actualHole,index,holeInside,_,actualLocal,_,_⟩ := base.indices
  have holeSame : actualHole = hole := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualLocal.symm.trans holeLocal
  have inside : hole.toNat < capacity.toNat := by simpa [holeSame] using holeInside
  have positive : 0 < items.toNat := by omega
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  obtain ⟨lastSlot,lastCell,lastInside⟩ := base.ordered (items - 1) (by omega)
  obtain ⟨cell,cellMemory⟩ : ∃ cell, scanned.memory (panByteAlignHOL (used + hole)) = HolWordLab.word cell := by
    cases scanned.memory (panByteAlignHOL (used + hole)) with
    | word cell => exact ⟨cell,rfl⟩
  have scannedReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer scanned := by
    rw [metaSame]
    exact metaReady
  obtain ⟨post,tail,preserved,ticks,globals,code,domain,endian⟩ := evaluate_hashDelete_final_tail_disjoint32 scanned
    table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    base.arrays inside lastInside positive deletedBound cellMemory lastCell
    (tFrame.trans tableLocal) base.orderLocal base.reverseLocal saved base.usedLocal holeLocal
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits scannedReady separated
  have scannedGlobals : scanned.globals = state.globals := by rw [metaSame]; exact metaGlobals
  have scannedCode : scanned.code = state.code := by rw [metaSame]; exact metaCode
  have scannedDomain : scanned.memaddrs = state.memaddrs := by rw [metaSame]; exact metaDomain
  have scannedEndian : scanned.be = state.be := by rw [metaSame]; exact metaEndian
  refine ⟨post,?_,preserved,by omega,by omega,globals.trans scannedGlobals,code.trans scannedCode,domain.trans scannedDomain,endian.trans scannedEndian⟩
  rw [evaluateHOLFiniteState_seq_line780,scanRun]
  exact tail


#print axioms evaluate_hashDelete_scan_tail_other32
end InitECandidate.Runtime

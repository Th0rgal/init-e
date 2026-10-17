import InitECandidate.Runtime.HashTableReadyMemcpy
import InitECandidate.Runtime.RollbackPhysicalSeparated
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A copy beyond all live table arrays preserves the complete registry and
its physical separation, with a memory frame for the journal prefix. -/
theorem rollback_registry_memcpy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (witness : BitVec 64)
    (member : witness ∈ tables)
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64) (destination source size : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (outside : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      reverse.toNat + capacity.toNat * 8 ≤ destination.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      (∀ table ∈ tables, RollbackTableReady widths table post) ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      (∀ watched : BitVec 64, watched.toNat < destination.toNat ∨ destination.toNat + size.toNat ≤ watched.toNat → post.memory watched = state.memory watched) := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,smallStride,large⟩ := family witness member
  obtain ⟨post,run,_,cost,remaining,globals,code,domain,endian,locals⟩ := ready.memcpy_outside state (widths witness) witness pointer keys stride capacity used values order reverse items bits
    destinationArgument sourceArgument sizeArgument destination source size small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
    (Or.inr (outside witness member pointer keys stride capacity used values order reverse items bits ready)) arguments
  have retains : ∀ table ∈ tables, ∀ op ok os oc ou ov oo orev oi ob,
      HashTableReady (widths table) table ok os oc ou ov oo orev oi ob op state →
      HashTableReady (widths table) table ok os oc ou ov oo orev oi ob op post := by
    intro table belongs op ok os oc ou ov oo orev oi ob oldReady
    obtain ⟨checked,checkedRun,checkedReady,_⟩ := oldReady.memcpy_outside state (widths table) table op ok os oc ou ov oo orev oi ob
      destinationArgument sourceArgument sizeArgument destination source size small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
      (Or.inr (outside table belongs op ok os oc ou ov oo orev oi ob oldReady)) arguments
    have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
    rw [same]
    exact checkedReady
  have postFamily : ∀ table ∈ tables, RollbackTableReady widths table post := by
    intro table belongs
    obtain ⟨op,ok,os,oc,ou,ov,oo,orev,oi,ob,oldReady,smallStride,large⟩ := family table belongs
    exact ⟨op,ok,os,oc,ou,ov,oo,orev,oi,ob,retains table belongs op ok os oc ou ov oo orev oi ob oldReady,smallStride,large⟩
  have postSep : RollbackPhysicalSeparated widths tables post := by
    apply separated.of_footprint_subset
    intro table belongs address inside
    obtain ⟨op,ok,os,oc,ou,ov,oo,orev,oi,ob,oldReady,_,_⟩ := family table belongs
    have newReady := retains table belongs op ok os oc ou ov oo orev oi ob oldReady
    exact (oldReady.rollback_footprint_iff state widths table op ok os oc ou ov oo orev oi ob address).mpr
      ((newReady.rollback_footprint_iff post widths table op ok os oc ou ov oo orev oi ob address).mp inside)
  refine ⟨post,run,postFamily,postSep,cost,remaining,globals,code,domain,endian,locals,?_⟩
  intro watched outsideCopy
  have apart := memcpy_interval_separate destination size watched aligned small outsideCopy
  obtain ⟨checked,checkedRun,cell,_⟩ := evaluate_memcpy_aligned_frame_call state destinationArgument sourceArgument sizeArgument destination source size watched
    small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
    (fun offset inside => (apart offset inside).1) (fun offset inside => (apart offset inside).2) ready.live.arrays.code arguments
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [same]
  exact cell

#print axioms rollback_registry_memcpy
end InitECandidate.Runtime

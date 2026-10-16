import InitECandidate.Runtime.HashProbeLoopFrame
import InitECandidate.Runtime.HashInsertTailReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty-slot readiness is a table invariant over actual memory and caller
locals. Probing supplies a concrete empty slot and transfers that invariant
through its memory-preserving, index-only state changes. -/
theorem evaluate_hashInsert_probe_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count keysIndex : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word keysIndex)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (inside : keysIndex.toNat < capacity.toNat) (budget : capacity.toNat ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (prepared : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot = some 0 →
      ∃ cell : BitVec 64, HashInsertTailReady capacity used table values value order orderPos count slot cell
        (setVarHOLFinite (ofString "i") (.val (.word slot)) state)) :
    ∃ post slot cell, evaluateHOLFiniteState state hashProbeLoop = (none,post) ∧
      state.clock < post.clock + capacity.toNat ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      HashInsertTailReady capacity used table values value order orderPos count slot cell post ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) := by
  obtain ⟨post,run,cost,remaining,memory,globals,code,addresses,endian,slot,slotLocal,slotInside,empty,other⟩ :=
    evaluate_hashProbeLoop_capacity_frame state capacity used keysIndex bits power indexLocal capacityLocal usedLocal inside budget readable room
  obtain ⟨cell,ready⟩ := prepared slot slotInside empty
  have locals : post.locals = (setVarHOLFinite (ofString "i") (.val (.word slot)) state).locals := by
    apply HolFiniteMapExact.ext
    funext name
    by_cases same : name = ofString "i"
    · subst name
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using slotLocal
    · rw [other name same]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same]
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext index
    unfold hashOccupancyRead
    rw [memory,addresses,endian]
  have counts : hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) := by
    rw [reads]
  have afterProbe := HashInsertTailReady.after_copy capacity used table values value order orderPos count slot cell
    (setVarHOLFinite (ofString "i") (.val (.word slot)) state) post ready locals addresses endian
    (congrArg (fun mem => mem (table + 40)) memory) (congrArg (fun mem => mem (table + 24)) memory)
    (congrArg (fun mem => mem (panByteAlignHOL (used + slot))) memory) counts
  exact ⟨post,slot,cell,run,cost,remaining,memory,globals,code,addresses,endian,afterProbe,other⟩

#print axioms evaluate_hashInsert_probe_ready
end InitECandidate.Runtime

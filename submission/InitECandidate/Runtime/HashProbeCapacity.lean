import InitECandidate.Runtime.HashOccupancy
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def hashOccupancyRead {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used index : BitVec 64) : Option UInt8 :=
  @panMemLoadByteHOL 64 _ state.memory state.memaddrs
    (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index)

/-- The source insertion probe terminates in fewer than capacity clocks when
its actual occupancy count is below capacity. No empty-slot witness is supplied. -/
theorem evaluate_hashProbeLoop_capacity {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used index : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (inside : index.toNat < capacity.toNat) (clock : capacity.toNat ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashProbeLoop = (none,post) ∧
      state.clock < post.clock + capacity.toNat ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      ∃ finalIndex : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        finalIndex.toNat < capacity.toNat ∧ hashOccupancyRead state used finalIndex = some 0 ∧
        ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) room
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat inside emptyInside
  obtain ⟨post,run,cost,remaining,memory,globals,code,domain,final⟩ :=
    evaluate_hashProbeLoop_bounded capacity empty used bits power emptyInside _ state index
      indexLocal capacityLocal usedLocal inside rfl (by omega) readable emptyLoad
  exact ⟨post,run,by omega,remaining,memory,globals,code,domain,final⟩

/-- Zero initialization establishes a count of zero for the actual byte reads. -/
theorem hashOccupiedCount_zero (capacity : BitVec 64) (read : BitVec 64 → Option UInt8)
    (zero : ∀ index : BitVec 64, index.toNat < capacity.toNat → read index = some 0) :
    hashOccupiedCount capacity read = 0 := by
  unfold hashOccupiedCount
  apply List.countP_eq_zero.mpr
  intro index member
  have bound : index < capacity.toNat := List.mem_range.mp member
  have wordBound : index < 2 ^ 64 := Nat.lt_trans bound capacity.isLt
  have loaded := zero (BitVec.ofNat 64 index) (by simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt wordBound] using bound)
  simp [loaded]

#print axioms evaluate_hashProbeLoop_capacity
#print axioms hashOccupiedCount_zero
end InitECandidate.Runtime

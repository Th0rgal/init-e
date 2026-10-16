import InitECandidate.Runtime.HashFindReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashFindLoop : ProgHOL 64 :=
  .while (hashProbeOccupied (ofString "i")) hashFindIteration

/-- Unroll one occupied lookup slot, including the while guard and actual
comparison call. Clock clamping is discharged from the exact two-clock cost. -/
theorem evaluate_hashFind_occupied32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride key index capacity used : BitVec 64) (byte : UInt8)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (inside : index.toNat < capacity.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte)
    (occupied : BitVec.ofNat 64 byte.toNat ≠ 0) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop =
        (match result with | none => evaluateHOLFiniteState post hashFindLoop | some _ => (result,post)) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock = state.clock - 2 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  have condition := eval_hashProbeOccupied state (ofString "i") index used byte indexLocal usedLocal loaded
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 byte.toNat) 0 = true := by
    have nonzero : BitVec.ofNat 64 byte.toNat ≠ (0#64) := occupied
    simp [Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  obtain ⟨result,post,body,outcome,ticks,memory,globals,postCode,addresses,endian,next,locals⟩ :=
    evaluate_hashFind_ready32 (decClockHOLFinite state) keys stride key index capacity code
      (by change state.clock - 1 ≠ 0; omega) keysAligned strideAligned keyAligned strideFits inside bounded
      arrayDomain keyDomain keysLocal strideLocal keyLocal lengthLocal indexLocal capLocal
  have ticks' : post.clock = state.clock - 2 := by
    change post.clock = state.clock - 1 - 1 at ticks
    omega
  refine ⟨result,post,?_,outcome,ticks',memory,globals,postCode,addresses,endian,next,locals⟩
  unfold hashFindLoop
  rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rw [if_pos flag]
  simp only [show state.clock ≠ 0 by omega,if_false,body]
  have fixed : fixClockHOLFinite (decClockHOLFinite state) (result,post) = (result,post) := by
    simp [fixClockHOLFinite,decClockHOLFinite,show ¬ state.clock - 1 < post.clock by omega]
  rw [fixed]
  rcases outcome with noneResult | returnedResult
  · rw [noneResult]
    rfl
  · rw [returnedResult]
    rfl

/-- The first empty occupancy slot exits the original lookup loop without
spending a clock or changing any state field. -/
theorem evaluate_hashFind_empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used index : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some 0) :
    evaluateHOLFiniteState state hashFindLoop = (none,state) := by
  have condition := eval_hashProbeOccupied state (ofString "i") index used 0 indexLocal usedLocal loaded
  unfold hashFindLoop
  rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rfl

/-- Two clocks per occupied slot suffice for the strictly decreasing cyclic
probe rank, including the comparison call and while guard. -/
theorem hashFind_rank_budget (capacity index empty : BitVec 64) (bits clock : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat) (different : index ≠ empty)
    (budget : 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ clock) :
    2 ≤ clock ∧
      2 * hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat ≤ clock - 2 := by
  have naturalDifferent : index.toNat ≠ empty.toNat := by
    intro equal; exact different (BitVec.eq_of_toNat_eq equal)
  have smaller : hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat <
      hashProbeDistance capacity.toNat index.toNat empty.toNat := by
    rw [hashProbeNext_wrap index capacity bits power inside]
    exact hashProbeDistance_decreases _ _ _ inside emptyInside naturalDifferent
  omega

#print axioms evaluate_hashFind_empty
#print axioms hashFind_rank_budget
#print axioms evaluate_hashFind_occupied32
end InitECandidate.Runtime

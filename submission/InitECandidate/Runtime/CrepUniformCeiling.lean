import InitECandidate.Runtime.CrepCeilingCall
namespace InitECandidate.Runtime
open Flapjack

theorem crep_leaf_ceiling {width : Nat} [NeZero width] {F : Type}
    {p : CrepProgHOL width} {s : CrepSemHOLState width F} {cost : Nat}
    (run : BoundedCrepPropertyAt p s cost) (small : cost ≤ sizeOf p) (limit : Nat) :
    BoundedCrepPropertyAt p s (workCeiling limit s.clock (sizeOf p)) := by
  apply crep_bounded_mono run
  have hp := crep_rank_pow (workRank limit s.clock (sizeOf p))
  have up : 8 ^ workRank limit s.clock (sizeOf p) ≤ workCeiling limit s.clock (sizeOf p) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  have nodes : sizeOf p ≤ workRank limit s.clock (sizeOf p) := by unfold workRank; omega
  omega

/-- Every original Crep constructor admits the uniform numerical ceiling once
strictly smaller evaluation obligations have their ceilings. -/
theorem crep_of_ceilingIH {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s)
    (ih : CrepCeilingIH limit p s) :
    BoundedCrepPropertyAt p s (workCeiling limit s.clock (sizeOf p)) := by
  cases p
  case seq a b => exact crep_seq_ceiling limit a b s small bounded ih
  case dec name e body => exact crep_dec_ceiling limit name e body s small bounded ih
  case ite e yes no => exact crep_if_ceiling limit e yes no s small bounded ih
  case «while» e body => exact crep_while_ceiling limit e body s small bounded ih
  case call ret name es => exact crep_call_ceiling limit ret name es s small bounded ih
  case «skip»  =>
    apply crep_leaf_ceiling (crep_skip_bounded s) ?_ limit
    simp
  case «break» label =>
    apply crep_leaf_ceiling (crep_break_bounded label s) ?_ limit
    simp
  case «continue» label =>
    apply crep_leaf_ceiling (crep_continue_bounded label s) ?_ limit
    simp
  case «tick»  =>
    apply crep_leaf_ceiling (crep_tick_bounded s) ?_ limit
    simp
  case «raise» eid =>
    apply crep_leaf_ceiling (crep_raise_bounded eid s) ?_ limit
    simp
  case «primitive» dest op args =>
    apply crep_leaf_ceiling (crep_primitive_bounded dest args op s) ?_ limit
    simp
  case «assign» name e =>
    apply crep_leaf_ceiling (crep_assign_bounded name e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.assign.sizeOf_spec]
    omega
  case «storeGlob» address e =>
    apply crep_leaf_ceiling (crep_storeGlob_bounded address e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.storeGlob.sizeOf_spec]
    omega
  case «shMem» op name e =>
    apply crep_leaf_ceiling (crep_shMem_bounded op name e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.shMem.sizeOf_spec]
    omega
  case «return» es =>
    apply crep_leaf_ceiling (crep_return_bounded es s) ?_ limit
    have h := crepExpsFuel_le_size es
    simp only [CrepProgHOL.return.sizeOf_spec]
    omega
  case store dst src =>
    apply crep_leaf_ceiling (crep_store_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.store.sizeOf_spec]
    omega
  case store32 dst src =>
    apply crep_leaf_ceiling (crep_store32_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.store32.sizeOf_spec]
    omega
  case storeByte dst src =>
    apply crep_leaf_ceiling (crep_storeByte_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.storeByte.sizeOf_spec]
    omega
  case extCall f ptr len arr alen =>
    apply crep_leaf_ceiling (cost := 0) ?_ (Nat.zero_le _) limit
    intro result post target ctxt live hr hg hs hm hgl hc hl
    exact crep_extCall_bounded f ptr len arr alen s result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩

/-- Full Crep-to-Loop simulation with a numerical extra-clock ceiling. All
recursive obligations are discharged on the actual clock/syntax rank. -/
theorem crep_uniform_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s) :
    BoundedCrepPropertyAt p s (workCeiling limit s.clock (sizeOf p)) := by
  have children : CrepCeilingIH limit p s := by
    intro child next smaller childSize nextBounded
    exact crep_bounded_mono (crep_uniform_ceiling limit child next childSize nextBounded)
      (workCeiling_child _ _ _ _ _ smaller)
  exact crep_of_ceilingIH limit p s small bounded children
termination_by workRank limit s.clock (sizeOf p)

#print axioms crep_of_ceilingIH
#print axioms crep_uniform_ceiling
end InitECandidate.Runtime

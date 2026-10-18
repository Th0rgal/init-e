import InitECandidate.Runtime.CrepAffineCall
import InitECandidate.Runtime.CrepUniformCeiling
namespace InitECandidate.Runtime
open Flapjack

/-- Every original Crep constructor admits the affine budget once strictly
smaller evaluation obligations have theirs. -/
theorem crep_of_affineIH {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s)
    (ih : CrepAffineIH limit p s) :
    BoundedCrepPropertyAt p s (crepAffine limit p s) := by
  cases p
  case seq a b => exact crep_seq_affine limit a b s small bounded ih
  case dec name e body => exact crep_dec_affine limit name e body s small bounded ih
  case ite e yes no => exact crep_if_affine limit e yes no s small bounded ih
  case «while» e body => exact crep_while_affine limit e body s small bounded ih
  case call ret name es => exact crep_call_affine limit ret name es s small bounded ih
  case «skip»  =>
    apply crep_leaf_affine (crep_skip_bounded s) ?_ limit
    simp
  case «break» label =>
    apply crep_leaf_affine (crep_break_bounded label s) ?_ limit
    simp
  case «continue» label =>
    apply crep_leaf_affine (crep_continue_bounded label s) ?_ limit
    simp
  case «tick»  =>
    apply crep_leaf_affine (crep_tick_bounded s) ?_ limit
    simp
  case «raise» eid =>
    apply crep_leaf_affine (crep_raise_bounded eid s) ?_ limit
    simp
  case «primitive» dest op args =>
    apply crep_leaf_affine (crep_primitive_bounded dest args op s) ?_ limit
    simp
  case «assign» name e =>
    apply crep_leaf_affine (crep_assign_bounded name e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.assign.sizeOf_spec]
    omega
  case «storeGlob» address e =>
    apply crep_leaf_affine (crep_storeGlob_bounded address e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.storeGlob.sizeOf_spec]
    omega
  case «shMem» op name e =>
    apply crep_leaf_affine (crep_shMem_bounded op name e s) ?_ limit
    have h := crepExprFuel_le_size e
    simp only [CrepProgHOL.shMem.sizeOf_spec]
    omega
  case «return» es =>
    apply crep_leaf_affine (crep_return_bounded es s) ?_ limit
    have h := crepExpsFuel_le_size es
    simp only [CrepProgHOL.return.sizeOf_spec]
    omega
  case store dst src =>
    apply crep_leaf_affine (crep_store_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.store.sizeOf_spec]
    omega
  case store32 dst src =>
    apply crep_leaf_affine (crep_store32_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.store32.sizeOf_spec]
    omega
  case storeByte dst src =>
    apply crep_leaf_affine (crep_storeByte_bounded dst src s) ?_ limit
    have hd := crepExprFuel_le_size dst
    have hs := crepExprFuel_le_size src
    simp only [CrepProgHOL.storeByte.sizeOf_spec]
    omega
  case extCall f ptr len arr alen =>
    apply crep_leaf_affine (cost := 0) ?_ (Nat.zero_le _) limit
    intro result post target ctxt live hr hg hs hm hgl hc hl
    exact crep_extCall_bounded f ptr len arr alen s result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩

/-- Full Crep-to-Loop simulation whose extra target clock is affine in the
source clock actually consumed: (5L+5)*(consumed) + 2*sizeOf program. -/
theorem crep_affine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s) :
    BoundedCrepPropertyAt p s (crepAffine limit p s) := by
  have children : CrepAffineIH limit p s := by
    intro child next smaller childSize nextBounded
    exact crep_affine limit child next childSize nextBounded
  exact crep_of_affineIH limit p s small bounded children
termination_by workRank limit s.clock (sizeOf p)

/-- Initial-fuel form: extra target clock at most (5L+5)*clock + 2L. -/
theorem crep_affine_fuel {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s) :
    BoundedCrepPropertyAt p s ((5 * limit + 5) * s.clock + 2 * limit) := by
  apply crep_bounded_mono (crep_affine limit p s small bounded)
  unfold crepAffine
  have clock := Nat.mul_le_mul_left (5 * limit + 5)
    (Nat.sub_le s.clock (evalCrepSemHOLProgExact s p).2.clock)
  omega

#print axioms crep_of_affineIH
#print axioms crep_affine
#print axioms crep_affine_fuel
end InitECandidate.Runtime

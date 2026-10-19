import InitECandidate.Runtime.KeccakFullCallWindow
import InitECandidate.Runtime.HtabMergeCore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hashing preserves an aligned table and its insertion order even on failure,
provided the real table footprint misses the three hash write windows. -/
theorem keccak_call_htab_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64) (arguments : List (ExpHOL 64))
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (ordered : OrderInv state capacity count used order orderPos)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word size),.val (.word output)])
    (small : size.toNat ≤ 134217712) (budget : size.toNat * 20 + 43 ≤ state.clock)
    (separate : ∀ watched : BitVec 64, HtabFoot table capacity used order orderPos watched.toNat →
      ¬ MWin pointer 200 watched ∧ ¬ MWin pad 136 watched ∧ ¬ MWin output 32 watched) :
    let post := (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") arguments)).2
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits post ∧
      OrderInv post capacity count used order orderPos := by
  let post := (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") arguments)).2
  have keep (w : BitVec 64) (foot : HtabFoot table capacity used order orderPos w.toNat) : post.memory w = state.memory w := by
    obtain ⟨oState,oPad,oOut⟩ := separate w foot
    exact (keccak_full_call_window state pointer pad source size output w arguments atState atPad args small inv.code budget
      oState oPad oOut).1
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "keccak256") arguments)
  have kept := inv.toRegions.foot_keep (r := post) keep
  exact ⟨inv.congr meta'.2.1 meta'.2.2.1 meta'.1 kept.1 kept.2.1,
    ordered.congr inv.toRegions.count_le meta'.2.1 meta'.2.2.1 kept.2.1 kept.2.2.1 kept.2.2.2⟩

#print axioms keccak_call_htab_frame
end InitECandidate.Runtime

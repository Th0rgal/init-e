import InitECandidate.Runtime.NodedbValueFrame
import InitECandidate.Runtime.KeccakFullCallWindow
import InitECandidate.Runtime.NodedbWindowGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual insertion hash call preserves every table value's witness
membership because its three write windows lie below the table allocation. -/
theorem nodedb_hash_values {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64) (arguments : List (ExpHOL 64))
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (targets : Set (BitVec 64))
    (inv : HtabAligned 32 table keys stride capacity used values order orderPos count bits s)
    (ordered : OrderInv s capacity count used order orderPos)
    (vt : VTabs targets s capacity count used keys stride values order)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some [.val (.word source),.val (.word size),.val (.word output)])
    (small : size.toNat ≤ 134217712) (budget : size.toNat * 20 + 43 ≤ s.clock)
    (stateBelow : pointer.toNat + 200 ≤ table.toNat) (padBelow : pad.toNat + 136 ≤ table.toNat)
    (outputBelow : output.toNat + 32 ≤ table.toNat) :
    VTabs targets (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "keccak256") arguments)).2
      capacity count used keys stride values order := by
  have metadata := evaluateHOLFiniteState_metadata s
    (.call (some (none,none)) (ofString "keccak256") arguments)
  apply vt.after_table_frame s _ targets 32 table keys stride capacity used values order orderPos count bits
    inv ordered metadata.2.1 metadata.2.2.1
  intro watched lower upper
  exact (keccak_full_call_window s pointer pad source size output watched arguments atState atPad args small
    inv.code budget (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))).1

#print axioms nodedb_hash_values
end InitECandidate.Runtime

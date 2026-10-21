import InitECandidate.Runtime.AllocCostSSAStageCases
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

/-!
# Compile-output bounds for leaf constructors

Bounds stated against the *actual* compile output `(ssaCcTrans p ssa next tables).1`
and the 64-bit native price `nativeWordPrice`, with the inserted-move overhead
*derived* from the emitted program rather than supplied as a target budget.

For `move` the compiler renames both sides of each pair and only updates the SSA
map (`force` is applied with `forceRename` to the map, not inserted as
instructions), so the emitted program is again a single `move` whose pair count
equals the source pair count.  Since `nativeWordPrice` on a `move` depends only
on that count, no moves are inserted and the executed cost is unchanged.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-- The native price of a `move` depends only on the number of pairs. -/
theorem nativeWordPrice_move_length {C F : Type} (pri : Nat)
    (ls ls' : List (Nat × Nat))
    (source target : WordSemStateFiniteExact 64 C F) (hlen : ls'.length = ls.length) :
    nativeWordPrice (.move pri ls') target = nativeWordPrice (.move pri ls) source := by
  rw [nativeWordPrice_move, nativeWordPrice_move, hlen]

/-- **Compiled `move` bound.**  If the compiler emits a `move` with the same
number of pairs, the executed cost is exactly the source cost: the renaming is
free because the parallel-move unit is priced by pair count alone. -/
theorem ssaCcTrans_move_cost {C F : Type} (pri : Nat) (ls : List (Nat × Nat))
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ls' : List (Nat × Nat)) (source target : WordSemStateFiniteExact 64 C F)
    (hcomp : (ssaCcTrans ((.move pri ls) : WordLangProgHOL (BitVec 64)) ssa na tables).1 =
      .move pri ls')
    (hlen : ls'.length = ls.length) :
    wordExecutionCost nativeWordPrice (.move pri ls') target ≤
      wordExecutionCost nativeWordPrice (.move pri ls) source := by
  rw [wec_move, wec_move, nativeWordPrice_move_length pri ls ls' source target hlen]

/-- **Compiled `inst` bound.**  If the compiler emits a single `inst`, the two
executed costs are the two node prices; whenever the emitted instruction's price
agrees with the source instruction's price the transfer is an equality. -/
theorem ssaCcTrans_inst_cost {C F : Type} (i i' : WordLangInst (BitVec 64))
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : WordSemStateFiniteExact 64 C F)
    (hcomp : (ssaCcTrans (.inst i) ssa na tables).1 = .inst i')
    (hprice : nativeWordPrice (.inst i') target = nativeWordPrice (.inst i) source) :
    wordExecutionCost nativeWordPrice (.inst i') target ≤
      wordExecutionCost nativeWordPrice (.inst i) source := by
  rw [wec_inst, wec_inst]
  exact le_of_eq hprice

#print axioms nativeWordPrice_move_length
#print axioms ssaCcTrans_move_cost
#print axioms ssaCcTrans_inst_cost

end InitECandidate.Runtime.FineCost

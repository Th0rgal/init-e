import InitECandidate.Runtime.HashGrowRehashSyntax
import InitECandidate.Runtime.HashGrowAllocationPlan
import InitECandidate.Runtime.MemzeroSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Heap-bounded rehash counters have nonnegative signed interpretations. -/
theorem hashGrow_signed_guard (index items : BitVec 64)
    (inside : index.toNat ≤ items.toNat) (small : items.toNat ≤ 33806089496) :
    Compiler.Encoders.Asm.wordCmpHOL .less index items = decide (index.toNat < items.toNat) := by
  have left : index.toNat < 2 ^ (64 - 1) := by omega
  have right : items.toNat < 2 ^ (64 - 1) := by omega
  simp only [Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,if_pos left,if_pos right]

/-- Evaluate the exact signed loop guard from its source locals. -/
theorem eval_hashGrow_rehash_condition {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index items : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (itemsLocal : state.locals.lookup (ofString "nitems") = some (.val (.word items)))
    (inside : index.toNat ≤ items.toNat) (small : items.toNat ≤ 33806089496) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .less (.var .local (ofString "k")) (.var .local (ofString "nitems"))) =
      some (.val (.word (if index.toNat < items.toNat then 1 else 0))) := by
  simp only [evalHOLExact]
  rw [indexLocal,itemsLocal]
  dsimp only
  rw [hashGrow_signed_guard index items inside small]
  simp

/-- The literal source counter update has no clock or memory effect. -/
theorem evaluate_hashGrow_rehash_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64)
    (binding : state.locals.lookup (ofString "k") = some (.val (.word index))) :
    evaluateHOLFiniteState state (.assign .local (ofString "k")
      (.op .add [.var .local (ofString "k"),.const 1])) =
      (none,setVarHOLFinite (ofString "k") (.val (.word (index + 1))) state) := by
  simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,
    valueIsWord,valueWord,isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

/-- Every taken rehash iteration decreases the remaining-item rank exactly
by one, with no 64-bit wrap in the original counter addition. -/
theorem hashGrow_rehash_rank (index items : BitVec 64)
    (inside : index.toNat < items.toNat) (small : items.toNat ≤ 33806089496) :
    (index + (1 : BitVec 64)).toNat = index.toNat + 1 ∧
      (index + 1).toNat ≤ items.toNat ∧
      items.toNat - (index + 1).toNat + 1 = items.toNat - index.toNat := by
  have advanced : (index + (1 : BitVec 64)).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
    rfl
  exact ⟨advanced,by omega,by omega⟩

/-- Rehashing at most the old capacity leaves room after each insertion into
the doubled table, discharging insertion's successor-count invariant premise. -/
theorem hashGrow_rehash_room (pointer capacity stride index items : BitVec 64)
    (strideBound : stride.toNat ≤ 56)
    (budget : pointer.toNat + 162 * capacity.toNat + 35 ≤ 33806089496)
    (itemsBound : items.toNat ≤ capacity.toNat) (inside : index.toNat < items.toNat) :
    index.toNat + 1 < (capacity * (2 : BitVec 64)).toNat := by
  have doubled := (htabGrow_allocation_plan_safe pointer capacity stride strideBound budget).1
  rw [doubled]
  omega

#print axioms hashGrow_signed_guard
#print axioms eval_hashGrow_rehash_condition
#print axioms evaluate_hashGrow_rehash_advance
#print axioms hashGrow_rehash_rank
#print axioms hashGrow_rehash_room
end InitECandidate.Runtime

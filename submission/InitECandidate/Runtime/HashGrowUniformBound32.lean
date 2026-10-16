import InitECandidate.Runtime.HashGrowCallBound32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A numerical ceiling for one complete 32-byte-key growth call, using the
fixed heap limit for both capacity and live item count. -/
def hashGrowClockCeiling32 : Nat :=
  2 * 33806089496 + 7 + 33806089496 * (2 * 33806089496 + 36)

theorem hashGrow_clock_expression_bounded (capacity items : BitVec 64)
    (capacityBound : capacity.toNat ≤ 33806089496) (itemsBound : items.toNat ≤ capacity.toNat) :
    (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ≤ hashGrowClockCeiling32 := by
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 := by
    exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  rw [doubled]
  have product := Nat.mul_le_mul (show items.toNat ≤ 33806089496 by omega)
    (show capacity.toNat * 2 + 36 ≤ 2 * 33806089496 + 36 by omega)
  unfold hashGrowClockCeiling32
  omega

#print axioms hashGrow_clock_expression_bounded
theorem evaluate_htabGrow32_call_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : 32 ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : hashGrowClockCeiling32 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word (32 : BitVec 64))
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])).2.clock + hashGrowClockCeiling32 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])).2.clock ≤ state.clock := by
  have expression := hashGrow_clock_expression_bounded capacity items capacityBound old.itemsBound
  have bounded := evaluate_htabGrow32_call_bounded state table pointer capacity stride keys values order items bits tableArgument arguments
    code power old strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound (by omega) heap domain
    keyField cell16 cell8 cell32 cell40 cell56 cell24
  exact ⟨by have := bounded.1; omega,bounded.2⟩

#print axioms evaluate_htabGrow32_call_uniform_bounded
end InitECandidate.Runtime

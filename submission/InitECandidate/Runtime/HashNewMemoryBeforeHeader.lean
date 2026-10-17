import InitECandidate.Runtime.HashNewHeader
import InitECandidate.Runtime.HashNewOrderMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A constructor header write cannot touch an earlier allocation. -/
theorem sourceWriteWord_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table address value : BitVec 64) (offset : BitVec 64)
    (bounded : table.toNat + 72 ≤ 33806089496) (small : offset.toNat < 72)
    (before : address.toNat < table.toNat) :
    (sourceWriteWord state (table + offset) value).memory address = state.memory address := by
  have location : (table + offset).toNat = table.toNat + offset.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  have separate : address ≠ table + offset := by
    intro equal
    have same := congrArg BitVec.toNat equal
    rw [location] at same
    omega
  simp only [sourceWriteWord,if_neg separate]

/-- All four scalar stores preserve memory before the constructor's header. -/
theorem htabNewHeaderPost_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength stride capacity address : BitVec 64)
    (bounded : table.toNat + 72 ≤ 33806089496) (before : address.toNat < table.toNat) :
    (htabNewHeaderPost state table keyLength stride capacity).memory address = state.memory address := by
  unfold htabNewHeaderPost
  rw [sourceWriteWord_before_header _ table address 0 24 bounded (by decide) before,
    sourceWriteWord_before_header _ table address capacity 16 bounded (by decide) before,
    sourceWriteWord_before_header _ table address stride 8 bounded (by decide) before,
    sourceWriteWord_before_header _ table address keyLength 0 bounded (by decide) before]

/-- The final two array-pointer stores preserve earlier allocations. -/
theorem htabNew_order_memory_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity address : BitVec 64)
    (bounded : table.toNat + 72 ≤ 33806089496) (before : address.toNat < table.toNat) :
    (sourceWriteWord (sourceWriteWord state (table + 56) pointer)
      (table + 64) (allocationEnd pointer (capacity * 8))).memory address = state.memory address := by
  rw [sourceWriteWord_before_header _ table address _ 64 bounded (by decide) before,
    sourceWriteWord_before_header _ table address pointer 56 bounded (by decide) before]

#print axioms sourceWriteWord_before_header
#print axioms htabNewHeaderPost_before_header
#print axioms htabNew_order_memory_before_header
end InitECandidate.Runtime

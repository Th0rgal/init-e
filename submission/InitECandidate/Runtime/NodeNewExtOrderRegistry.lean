import InitECandidate.Runtime.NodeNewExtCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ExtensionRecordOrder {F : Type} (state : PanSemStateFiniteExact 64 F) (node : BitVec 64) : Prop :=
  ∀ child : BitVec 64, state.memory (node + 40) = .word 0 →
    state.memory (node + 48) = .word child → child.toNat < node.toNat

def ExtensionOrderFamily {F : Type} (nodes : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ node ∈ nodes, ExtensionRecordOrder state node

theorem extensionOrderFamily_empty {F : Type} (state : PanSemStateFiniteExact 64 F) :
    ExtensionOrderFamily ∅ state := by intro node member; cases member

/-- Fresh allocations preserve the order of complete older extension records. -/
theorem extensionOrderFamily_before_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (nodes : Set (BitVec 64)) (pointer : BitVec 64)
    (order : ExtensionOrderFamily nodes state)
    (headers : ∀ node ∈ nodes, node.toNat + 56 ≤ pointer.toNat)
    (frame : ∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) :
    ExtensionOrderFamily nodes post := by
  intro node member child empty loaded
  have bound := headers node member
  have natural (offset : Nat) (small : offset < 56) :
      (node + BitVec.ofNat 64 offset).toNat = node.toNat + offset := by
    have literal : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by have limit := pointer.isLt; rw [literal]; change node.toNat + offset < 2^64; omega),literal]
  have forty : (node + (40 : BitVec 64)).toNat < pointer.toNat := by
    change (node + BitVec.ofNat 64 40).toNat < pointer.toNat
    rw [natural 40 (by decide)]
    omega
  have fortyEight : (node + (48 : BitVec 64)).toNat < pointer.toNat := by
    change (node + BitVec.ofNat 64 48).toNat < pointer.toNat
    rw [natural 48 (by decide)]
    omega
  exact order node member child ((frame _ forty).symm.trans empty) ((frame _ fortyEight).symm.trans loaded)

/-- The actual constructor call adds a fresh extension to the order registry
and keeps every old and new record below the updated allocation frontier. -/
theorem evaluate_nodeNewExt_order_registry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nodes : Set (BitVec 64)) (nibArgument sizeArgument childArgument : ExpHOL 64)
    (pointer nib size child : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [nibArgument,sizeArgument,childArgument] = some [.val (.word nib),.val (.word size),.val (.word child)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (request : (56 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 56).toNat ≤ 33806089496)
    (recordBound : pointer.toNat + 56 ≤ 33806089496)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (childBefore : child.toNat < pointer.toNat)
    (order : ExtensionOrderFamily nodes state)
    (headers : ∀ node ∈ nodes, node.toNat + 56 ≤ pointer.toNat) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "node_new_ext") [nibArgument,sizeArgument,childArgument]) = (none,ready) ∧
      ready.clock = state.clock - 2 ∧ ExtensionOrderFamily (insert pointer nodes) ready ∧
      (∀ node ∈ insert pointer nodes, node.toNat + 56 ≤ (allocationEnd pointer 56).toNat) := by
  obtain ⟨ready,run,clock,_,_,_,_,_,before,newOrder,_⟩ := evaluate_nodeNewExt_call_and_declaration
    state nibArgument sizeArgument childArgument pointer nib size child args heap code ticks request finishBound recordBound domain childBefore
  have oldOrder := extensionOrderFamily_before_frame state ready nodes pointer order headers before
  have covers := (allocationEnd_covers pointer 56 (by change pointer.toNat + 56 ≤ 33806089496; exact recordBound)).1
  change pointer.toNat + 56 ≤ (allocationEnd pointer 56).toNat at covers
  refine ⟨ready,run,clock,?_,?_⟩
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact newOrder
    · exact oldOrder node old
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact covers
    · have bound := headers node old
      omega

#print axioms extensionOrderFamily_empty
#print axioms extensionOrderFamily_before_frame
#print axioms evaluate_nodeNewExt_order_registry
end InitECandidate.Runtime

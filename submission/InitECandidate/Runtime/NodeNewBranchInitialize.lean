import InitECandidate.Runtime.ZeroBranchChildren
import InitECandidate.Runtime.MemzeroAlignedCombinedCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodeNewBranchInitialize : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_node_new_branch with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

theorem source_nodeNewBranch_initialize : nodeNewBranchInitialize =
    .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "nd"),.const 176])
      (.seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 3))
        (.return (.var .local (ofString "nd")))) := by
  simp only [nodeNewBranchInitialize,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original post-allocation branch initializer zeroes all child slots,
sets kind 3, returns its pointer, and preserves memory before the record. -/
theorem evaluate_nodeNewBranch_initialize {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (ndLocal : state.locals.lookup (ofString "nd") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 177 ≤ state.clock)
    (bounded : pointer.toNat + 176 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 176 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state nodeNewBranchInitialize = (some (.returned (.val (.word pointer))),post) ∧
      state.clock ≤ post.clock + 177 ∧ post.clock ≤ state.clock ∧
      post.memory pointer = .word 3 ∧
      (∀ slot : Nat, slot < 16 → post.memory (branchChildAddress pointer slot) = .word 0) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "nd"),.const 176] = some [.val (.word pointer),.val (.word (176 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ndLocal]
  obtain ⟨zeroed,zeroRun,coverage,cost,remaining,globals,postCode,domain,endian,locals,_,frame⟩ :=
    evaluate_memzero_aligned_call_with_frame state _ _ pointer 176 args code ticks bounded aligned wordDomain byteDomain
  have ndZeroed : zeroed.locals.lookup (ofString "nd") = some (.val (.word pointer)) := by rw [locals]; exact ndLocal
  have address : @evalHOLExact 64 F _ zeroed.toExact
      (fun address => Classical.propDecidable (zeroed.memaddrs address))
      (.op .add [.var .local (ofString "nd"),.const 0]) = some (.val (.word pointer)) := by
    simp [evalHOLExact,evalListHOLExact,ndZeroed,wordOpHOL,wordOp,valueIsWord,valueWord]
  have pointerDomain : zeroed.memaddrs pointer := by
    rw [domain]
    simpa using wordDomain 0 (by decide)
  have store := evaluate_store_word zeroed pointer 3 _ (.const 3) address rfl pointerDomain
  let marked := sourceWriteWord zeroed pointer 3
  have returned : evaluateHOLFiniteState marked (.return (.var .local (ofString "nd"))) =
      (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite marked) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,marked,sourceWriteWord,ndZeroed,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite marked,?_,cost,remaining,?_,?_,globals,postCode,domain,endian,?_⟩
  · rw [source_nodeNewBranch_initialize]
    exact evaluate_seq_none zeroRun (evaluate_seq_none store returned)
  · simp [marked,sourceWriteWord,emptyLocalsHOLFinite]
  · intro slot small
    have zeroSlot := zeroBranch_child_slots zeroed pointer coverage aligned (by omega) slot small
    have separate : branchChildAddress pointer slot ≠ pointer := by
      intro equal
      have natural : (branchChildAddress pointer slot).toNat = pointer.toNat + 32 + slot * 8 := by
        unfold branchChildAddress
        rw [BitVec.toNat_add,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat]
        change ((pointer.toNat + 32) % 18446744073709551616 +
          (slot % 18446744073709551616 * 8) % 18446744073709551616) % 18446744073709551616 = pointer.toNat + 32 + slot * 8
        omega
      have same := congrArg BitVec.toNat equal
      rw [natural] at same
      omega
    simpa [marked,sourceWriteWord,emptyLocalsHOLFinite,separate] using zeroSlot
  · intro watched before
    have separate : watched ≠ pointer := by intro equal; subst watched; omega
    have memory := frame watched
      (by
        intro offset small equal
        change offset < 176 at small
        have literal : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat]; omega
        have natural : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
          rw [BitVec.toNat_add_of_lt (by rw [literal]; omega),literal]
        have same := congrArg BitVec.toNat equal
        rw [natural] at same
        omega)
      (by
        intro offset small equal
        change offset < 176 at small
        have inside : (BitVec.ofNat 64 offset).toNat < (176 : BitVec 64).toNat := by
          rw [BitVec.toNat_ofNat]; change offset % 18446744073709551616 < 176; omega
        have allocationBound : pointer.toNat + (176 : BitVec 64).toNat ≤ 2^64 := by
          change pointer.toNat + 176 ≤ 2^64
          omega
        have interval := hashOccupancy_aligned_interval pointer 176 (BitVec.ofNat 64 offset) aligned allocationBound inside
        have same := congrArg BitVec.toNat equal
        omega)
    simpa [marked,sourceWriteWord,emptyLocalsHOLFinite,separate] using memory

#print axioms source_nodeNewBranch_initialize
#print axioms evaluate_nodeNewBranch_initialize
end InitECandidate.Runtime

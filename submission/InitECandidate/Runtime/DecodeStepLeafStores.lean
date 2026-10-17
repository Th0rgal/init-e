import InitECandidate.Runtime.DecodeStepExtensionCheck
import InitECandidate.Runtime.TrieNibbleWordFrame
import InitECandidate.Runtime.TrieNodeMetadataStore
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepLeafStores : ProgHOL 64 :=
  match decodeStepLeafBranch with
  | .decCall _ _ _ _ (.seq _ (.decCall _ _ _ _ body)) => body
  | _ => .skip

theorem source_decodeStep_leaf_stores : decodeStepLeafStores =
    .seq (.store (.op .add [.var .local (ofString "lf"),.const 8]) (.var .local (ofString "p")))
      (.seq (.store (.op .add [.var .local (ofString "lf"),.const 16]) (.var .local (ofString "n")))
        (.return (.rstruct [.const 0,.var .local (ofString "lf")]))) := by
  simp only [decodeStepLeafStores,decodeStepLeafBranch,decodeStepCompactContinuation,decodeStepCompactCall,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def decodeStepLeafStoresPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (leaf pointer length : BitVec 64) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite (sourceWriteWord (sourceWriteWord state (leaf + 8) pointer) (leaf + 16) length)

/-- The original parser attaches its encoded bytes to the new leaf and
returns the leaf pointer without spending a source clock tick. -/
theorem evaluate_decodeStep_leaf_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (leaf pointer length : BitVec 64)
    (leafLocal : state.locals.lookup (ofString "lf") = some (.val (.word leaf)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (firstDomain : state.memaddrs (leaf + 8)) (secondDomain : state.memaddrs (leaf + 16)) :
    evaluateHOLFiniteState state decodeStepLeafStores =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),.val (.word leaf)])),
        decodeStepLeafStoresPost state leaf pointer length) := by
  let middle := sourceWriteWord state (leaf + 8) pointer
  have first : evaluateHOLFiniteState state
      (.store (.op .add [.var .local (ofString "lf"),.const 8]) (.var .local (ofString "p"))) = (none,middle) := by
    apply evaluate_store_word state (leaf + 8) pointer
    · simp [evalHOLExact,evalListHOLExact,leafLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · exact pointerLocal
    · exact firstDomain
  have second : evaluateHOLFiniteState middle
      (.store (.op .add [.var .local (ofString "lf"),.const 16]) (.var .local (ofString "n"))) =
      (none,sourceWriteWord middle (leaf + 16) length) := by
    apply evaluate_store_word middle (leaf + 16) length
    · simp [evalHOLExact,evalListHOLExact,leafLocal,wordOpHOL,wordOp,valueIsWord,valueWord,middle,sourceWriteWord]
    · exact lengthLocal
    · exact secondDomain
  rw [source_decodeStep_leaf_stores,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,leafLocal,shapeOfHOLExact,
    sizeOfShapeWithContextHOL,decodeStepLeafStoresPost,middle,sourceWriteWord]

/-- The parser's two leaf metadata writes preserve traversal registration
and any path whose containing words are separate from those metadata fields. -/
theorem decodeStepLeafStoresPost_invariants {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (leaf pointer length nibs count : BitVec 64)
    (member : leaf ∈ live) (capacity : 32 ≤ size leaf)
    (valid : TrieNibbleRange state nibs count)
    (outside : ∀ offset : Nat, offset < count.toNat →
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ leaf + 8 ∧
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ leaf + 16) :
    let post := decodeStepLeafStoresPost state leaf pointer length
    TrieWalkRegistry live extensions branches post ∧ TrieNibbleRange post nibs count ∧ post.clock = state.clock := by
  have firstRegistry := registry.write_metadata state live extensions branches size layout leaf pointer member capacity 8 (by decide) (by decide)
  have secondRegistry := firstRegistry.write_metadata _ live extensions branches size layout leaf length member capacity 16 (by decide) (by decide)
  have firstRange := valid.after_word_outside (leaf + 8) pointer (fun offset inside => (outside offset inside).1)
  have secondRange := firstRange.after_word_outside (leaf + 16) length (fun offset inside => (outside offset inside).2)
  exact ⟨secondRegistry.after_memory rfl,secondRange.after_frame rfl rfl rfl,rfl⟩

/-- A path allocated before the new leaf is automatically separate from
its metadata fields; the live layout supplies no-wrap bounds for the leaf. -/
theorem decodeStepLeafStoresPost_before_path {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (leaf pointer length nibs count : BitVec 64)
    (member : leaf ∈ live) (capacity : 32 ≤ size leaf)
    (valid : TrieNibbleRange state nibs count)
    (aligned : nibs.toNat % 8 = 0)
    (beforeLeaf : nibs.toNat + count.toNat ≤ leaf.toNat) :
    let post := decodeStepLeafStoresPost state leaf pointer length
    TrieWalkRegistry live extensions branches post ∧ TrieNibbleRange post nibs count ∧ post.clock = state.clock := by
  apply decodeStepLeafStoresPost_invariants state live extensions branches size layout registry
    leaf pointer length nibs count member capacity valid
  intro offset inside
  have offsetSmall : offset < 2^64 := by have top := count.isLt; omega
  have indexSmall : (BitVec.ofNat 64 offset).toNat < count.toNat := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
    exact inside
  have interval := hashOccupancy_aligned_interval nibs count (BitVec.ofNat 64 offset) aligned
    (by have top := leaf.isLt; omega) indexSmall
  have firstNat := layout.field_nat leaf member 8 (by omega)
  have secondNat := layout.field_nat leaf member 16 (by omega)
  constructor
  · intro equal
    have same := congrArg BitVec.toNat equal
    change (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)).toNat = (leaf + BitVec.ofNat 64 8).toNat at same
    rw [firstNat] at same
    omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    change (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)).toNat = (leaf + BitVec.ofNat 64 16).toNat at same
    rw [secondNat] at same
    omega

#print axioms decodeStepLeafStoresPost_before_path
#print axioms evaluate_decodeStep_leaf_stores
#print axioms decodeStepLeafStoresPost_invariants
end InitECandidate.Runtime

import InitECandidate.Runtime.DecodeStepLeafStores
import InitECandidate.Runtime.NodeNewLeafLayoutPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepLeafConstruction : ProgHOL 64 :=
  match decodeStepLeafBranch with
  | .decCall _ _ _ _ (.seq _ body) => body
  | _ => .skip

theorem source_decodeStep_leaf_construction : decodeStepLeafConstruction =
    .decCall (ofString "lf") .one (ofString "node_new_leaf")
      [.rfield 0 (.var .local (ofString "cn")),.rfield 1 (.var .local (ofString "cn")),
       .rfield 1 (.var .local (ofString "vi")),.rfield 2 (.var .local (ofString "vi"))] decodeStepLeafStores := by
  simp only [decodeStepLeafConstruction,decodeStepLeafStores,decodeStepLeafBranch,
    decodeStepCompactContinuation,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original parser leaf declaration, metadata writes and return compose
into a two-tick construction preserving the decoded path and trie invariants. -/
theorem evaluate_decodeStep_leaf_construction {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (leaf pointer length nibs count flag valuePointer valueLength valueKind consumed : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (valueLocal : state.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word valueKind),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word leaf)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (budget : leaf.toNat + 64 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (registry : TrieWalkRegistry live extensions branches state)
    (layout : TrieNodeLayout live extensions branches size)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ leaf.toNat)
    (path : TrieNibbleRange state nibs count)
    (aligned : nibs.toNat % 8 = 0)
    (pathBefore : nibs.toNat + count.toNat ≤ leaf.toNat) :
    ∃ post, evaluateHOLFiniteState state decodeStepLeafConstruction =
        (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),.val (.word leaf)])),post) ∧
      post.clock = state.clock - 2 ∧ TrieNibbleRange post nibs count ∧
      TrieWalkRegistry (insert leaf live) extensions branches post ∧
      TrieNodeLayout (insert leaf live) extensions branches (trieRecordSizeInsert size leaf 64) := by
  let a0 : ExpHOL 64 := .rfield 0 (.var .local (ofString "cn"))
  let a1 : ExpHOL 64 := .rfield 1 (.var .local (ofString "cn"))
  let a2 : ExpHOL 64 := .rfield 1 (.var .local (ofString "vi"))
  let a3 : ExpHOL 64 := .rfield 2 (.var .local (ofString "vi"))
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [a0,a1,a2,a3] = some [.val (.word nibs),.val (.word count),.val (.word valuePointer),.val (.word valueLength)] := by
    simp [a0,a1,a2,a3,evalListHOLFinite,evalListHOLExact,evalHOLExact,pathLocal,valueLocal]
  obtain ⟨ready,run,clock,locals,_,valid,registered,allocated,_⟩ := evaluate_nodeNewLeaf_layout_path state
    live extensions branches size a0 a1 a2 a3 leaf nibs count valuePointer valueLength args heap code ticks
    budget heapDomain registry layout path pathBefore frontier
  have request := allocationGuard_of_sum_bound leaf 64 (show leaf.toNat + (64 : BitVec 64).toNat ≤ 33806089496 from budget)
  have finish := allocationEnd_within_heap leaf 64 (by omega) request
  have domain : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), state.memaddrs (leaf + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 64 := by simp at member; omega
    have natural : (leaf + BitVec.ofNat 64 offset).toNat = leaf.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    exact heapDomain _ (by rw [natural]; omega)
  obtain ⟨other,otherRun,_,_,_,_,_,declaration⟩ := evaluate_nodeNewLeaf_call_and_declaration state
    a0 a1 a2 a3 leaf nibs count valuePointer valueLength args heap code ticks request finish budget domain
  have same : other = ready := (Prod.mk.inj (otherRun.symm.trans run)).2
  subst other
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "node_new_leaf") [a0,a1,a2,a3])
  rw [run] at metadata
  dsimp only at metadata
  let entered := setVarHOLFinite (ofString "lf") (.val (.word leaf)) ready
  have frame : ∀ name, name ≠ ofString "lf" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atLeaf : entered.locals.lookup (ofString "lf") = some (.val (.word leaf)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have firstDomain : entered.memaddrs (leaf + 8) := by
    change ready.memaddrs (leaf + 8)
    rw [metadata.2.1]
    exact domain 8 (by simp)
  have secondDomain : entered.memaddrs (leaf + 16) := by
    change ready.memaddrs (leaf + 16)
    rw [metadata.2.1]
    exact domain 16 (by simp)
  have stores := evaluate_decodeStep_leaf_stores entered leaf pointer length atLeaf
    ((frame _ (by decide)).trans pointerLocal) ((frame _ (by decide)).trans lengthLocal) firstDomain secondDomain
  have invariants := decodeStepLeafStoresPost_before_path entered (insert leaf live) extensions branches
    (trieRecordSizeInsert size leaf 64) allocated (registered.after_memory rfl) leaf pointer length nibs count
    (by simp) (by simp [trieRecordSizeInsert]) (valid.after_frame rfl rfl rfl) aligned pathBefore
  let output := decodeStepLeafStoresPost entered leaf pointer length
  let final := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "lf",state.locals.lookup (ofString "lf"))}
  refine ⟨final,?_,clock,invariants.2.1.after_frame rfl rfl rfl,invariants.1.after_memory rfl,allocated⟩
  rw [source_decodeStep_leaf_construction]
  change evaluateHOLFiniteState state (.decCall (ofString "lf") .one (ofString "node_new_leaf") [a0,a1,a2,a3] decodeStepLeafStores) = _
  rw [declaration]
  change (let result := evaluateHOLFiniteState entered decodeStepLeafStores; _) = _
  rw [stores]

#print axioms evaluate_decodeStep_leaf_construction
end InitECandidate.Runtime

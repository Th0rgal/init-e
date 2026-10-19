import InitECandidate.Runtime.StateInitWorldPrefix
import InitECandidate.Runtime.NodedbContentsHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual initializer world-record prefix preserves both original databases
and their bounded witness slices before witness decoding starts. -/
theorem state_init_world_database_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldWs nodes root codes nodeArray nodeCount codeArray codeCount input inputLength : BitVec 64)
    (tail : ProgHOL 64)
    (nodeTable : NodedbTableAt s nodes pointer nodeCount)
    (codeTable : NodedbTableAt s codes pointer codeCount)
    (nodeEntries : HashTableValuesIn nodes (NodedbSliceTargets nodeArray nodeCount) s)
    (codeEntries : HashTableValuesIn codes (NodedbSliceTargets codeArray codeCount) s)
    (nodeSlices : RlpSliceInputPrefix s nodeArray input inputLength nodeCount.toNat)
    (codeSlices : RlpSliceInputPrefix s codeArray input inputLength codeCount.toNat)
    (nodeEnd : nodeArray.toNat + nodeCount.toNat * 16 ≤ pointer.toNat)
    (codeEnd : codeArray.toNat + codeCount.toNat * 16 ≤ pointer.toNat)
    (code : s.code = originalRuntimeCode) (ticks : s.clock ≠ 0)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ws : s.globals.lookup (ofString "ws") = some (.val (.word oldWs)))
    (nodeLocal : s.locals.lookup (ofString "nodedb") = some (.val (.word nodes)))
    (rootLocal : s.locals.lookup (ofString "state_root") = some (.val (.word root)))
    (codeLocal : s.locals.lookup (ofString "codedb") = some (.val (.word codes)))
    (room : pointer.toNat + 48 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (stateInitWorldPrefix tail) = evaluateHOLFiniteState post tail ∧
      post.clock = s.clock - 1 ∧ post.locals = s.locals ∧ post.code = s.code ∧
      post.memaddrs = s.memaddrs ∧ post.be = s.be ∧
      post.globals.lookup (ofString "ws") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 40))) ∧
      NodedbTableAt post nodes (allocationEnd pointer 40) nodeCount ∧
      NodedbTableAt post codes (allocationEnd pointer 40) codeCount ∧
      HashTableValuesIn nodes (NodedbSliceTargets nodeArray nodeCount) post ∧
      HashTableValuesIn codes (NodedbSliceTargets codeArray codeCount) post ∧
      RlpSliceInputPrefix post nodeArray input inputLength nodeCount.toNat ∧
      RlpSliceInputPrefix post codeArray input inputLength codeCount.toNat ∧
      post.memory (pointer + 0) = .word nodes ∧ post.memory (pointer + 8) = .word root ∧
      post.memory (pointer + 16) = .word codes := by
  obtain ⟨post,run,clock,locals,installed,addresses,endian,atWs,atHeap,c0,c8,c16,frame,_⟩ :=
    evaluate_state_init_world_prefix s pointer oldWs nodes root codes tail code ticks heap ws nodeLocal rootLocal
      codeLocal room domain
  have covers := (allocationEnd_covers pointer 40 (by change pointer.toNat + 40 ≤ 33806089496; omega)).1
  have monotone : pointer.toNat ≤ (allocationEnd pointer 40).toNat := by
    change pointer.toNat + 40 ≤ _ at covers
    omega
  have nodesPost := nodedb_contents_after_heap_frame s post nodes pointer (allocationEnd pointer 40) nodeArray
    nodeCount input inputLength nodeTable nodeEntries nodeSlices nodeEnd monotone addresses endian installed frame
  have codesPost := nodedb_contents_after_heap_frame s post codes pointer (allocationEnd pointer 40) codeArray
    codeCount input inputLength codeTable codeEntries codeSlices codeEnd monotone addresses endian installed frame
  exact ⟨post,run,clock,locals,installed,addresses,endian,atWs,atHeap,nodesPost.1,codesPost.1,
    nodesPost.2.1,codesPost.2.1,nodesPost.2.2,codesPost.2.2,c0,c8,c16⟩

#print axioms state_init_world_database_contents
end InitECandidate.Runtime

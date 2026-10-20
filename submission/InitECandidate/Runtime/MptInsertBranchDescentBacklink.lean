import InitECandidate.Runtime.MptInsertBranchDescent
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The full original branch descent reads its nibble before selecting a live
child and preparing a typed backlink. The slot bound follows from the buffer. -/
theorem evaluate_mptInsert_branch_descent_backlink {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (registry : TrieWalkRegistry live extensions branches state)
    (node key level keyLength : BitVec 64) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (fits : level.toNat < keyLength.toNat) (nibbles : TrieNibbleRange state key keyLength)
    (keyDomain : state.memaddrs (panByteAlignHOL (key + level)))
    (childrenDomain : ∀ slot : Nat, slot < 16 → state.memaddrs (branchChildAddress node slot))
    (oldResult : BitVec 64) (oldResultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (oldNode : BitVec 64) (oldNodeLocal : state.locals.lookup (ofString "next_node") = some (.val (.word oldNode)))
    (oldSlot : BitVec 64) (oldSlotLocal : state.locals.lookup (ofString "next_slot") = some (.val (.word oldSlot)))
    (oldLevel : BitVec 64) (oldLevelLocal : state.locals.lookup (ofString "next_level") = some (.val (.word oldLevel)))
    (oldGo : BitVec 64) (oldGoLocal : state.locals.lookup (ofString "go") = some (.val (.word oldGo)))
    : ∃ post child slot,
      evaluateHOLFiniteState state mptInsertBranchDescent = (none,post) ∧
      post.locals.lookup (ofString "r") = some (.val (.word node)) ∧
      post.locals.lookup (ofString "next_node") = some (.val (.word child)) ∧ (child = 0 ∨ child ∈ live) ∧
      post.locals.lookup (ofString "next_slot") = some (.val (.word slot)) ∧ TrieChildSlot post extensions branches slot ∧
      post.locals.lookup (ofString "next_level") = some (.val (.word (level + 1))) ∧
      level.toNat < (level + 1).toNat ∧ (level + 1).toNat ≤ keyLength.toNat ∧
      post.locals.lookup (ofString "go") = some (.val (.word (1 : BitVec 64))) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock ∧
      post.memory slot = .word child := by
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64, state.memory (panByteAlignHOL (key + level)) = .word cell := by
    cases state.memory (panByteAlignHOL (key + level)) with | word cell => exact ⟨cell,rfl⟩
  let byte := panGetByteHOL (key + level) cell state.be
  have loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (key + level) = some byte := by
    simp [panMemLoadByteHOL,keyDomain,cellRead,byte]
  have small : byte.toNat < 16 := nibbles level.toNat fits byte (by simpa using loaded)
  obtain ⟨child,childField⟩ : ∃ child : BitVec 64, state.memory (branchChildAddress node byte.toNat) = .word child := by
    cases state.memory (branchChildAddress node byte.toNat) with | word child => exact ⟨child,rfl⟩
  let entered := setVarHOLFinite (ofString "idx") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have kept : ∀ name, name ≠ ofString "idx" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atIndex : entered.locals.lookup (ofString "idx") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨output,run,atResult,atChild,childValid,atSlot,slotTyped,atLevel,progress,bounded,atGo,memory,clock⟩ :=
    evaluate_mptInsert_branch_advance entered live extensions branches (registry.after_memory rfl)
      node level child keyLength byte.toNat small registered
      ((kept _ (by decide)).trans nodeLocal) ((kept _ (by decide)).trans levelLocal) atIndex
      childField (childrenDomain byte.toNat small) fits
      oldResult ((kept _ (by decide)).trans oldResultLocal)
      oldNode ((kept _ (by decide)).trans oldNodeLocal) oldSlot ((kept _ (by decide)).trans oldSlotLocal)
      oldLevel ((kept _ (by decide)).trans oldLevelLocal) oldGo ((kept _ (by decide)).trans oldGoLocal)
  have globals := evaluate_readOnly_globals mptInsertBranchAdvance
    (by rw [source_mptInsert_branch_advance];rfl) entered
  rw [run] at globals
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.op .add [.var .local (ofString "key"),.var .local (ofString "level")])) =
      some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,evalListHOLExact,keyLocal,levelLocal,wordOpHOL,wordOp,valueIsWord,valueWord,loaded]
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "idx",state.locals.lookup (ofString "idx"))}
  have restored : ∀ name, name ≠ ofString "idx" → post.locals.lookup name = output.locals.lookup name := by
    intro name different
    exact saved_local_lookup_other output.locals (ofString "idx") name _ different
  refine ⟨post,child,branchChildAddress node byte.toNat,?_,(restored _ (by decide)).trans atResult,
    (restored _ (by decide)).trans atChild,childValid,(restored _ (by decide)).trans atSlot,
    ?_,(restored _ (by decide)).trans atLevel,progress,bounded,(restored _ (by decide)).trans atGo,memory,globals,clock,?_⟩
  · rw [source_mptInsert_branch_descent,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered mptInsertBranchAdvance; _) = _
    rw [run]
  · exact Or.inl ⟨node,registered,byte.toNat,small,rfl⟩

  · change output.memory (branchChildAddress node byte.toNat)=.word child
    rw [memory]
    exact childField

#print axioms evaluate_mptInsert_branch_descent_backlink
end InitECandidate.Runtime

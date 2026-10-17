import InitECandidate.Runtime.TrieWalkBranchChild
import InitECandidate.Runtime.LoadOneRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def branchChildAddress (node : BitVec 64) (slot : Nat) : BitVec 64 := node + 32 + BitVec.ofNat 64 slot * 8

def trieWalkBranchChildAddressExpression : ExpHOL 64 :=
  .op .add [.var .local (ofString "node"),.const 32,
    .panop .mul [.loadByte (.op .add [.var .local (ofString "nibs"),.var .local (ofString "pos")]),.const 8]]

theorem source_trieWalk_branch_node_expression : trieWalkBranchNodeExpression =
    .load .one trieWalkBranchChildAddressExpression := by
  simp only [trieWalkBranchNodeExpression,trieWalkBranchAdvance,trieWalkBranchBranch,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem eval_trieWalk_branch_child_address {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs index : BitVec 64) (byte : UInt8)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (read : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + index) = some byte) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      trieWalkBranchChildAddressExpression = some (.val (.word (branchChildAddress node byte.toNat))) := by
  simp [trieWalkBranchChildAddressExpression,branchChildAddress,evalHOLExact,evalListHOLExact,nodeLocal,nibsLocal,posLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,read,BitVec.add_assoc]

/-- The actual normal branch update selects the slot indexed by its actual
loaded byte. The subsequent position update cannot change that child local. -/
theorem evaluate_trieWalk_branch_advance_child_address {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state trieWalkBranchAdvance = (none,post)) :
    ∃ byte : UInt8, ∃ child : BitVec 64,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + index) = some byte ∧
      state.memaddrs (branchChildAddress node byte.toNat) ∧
      state.memory (branchChildAddress node byte.toNat) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) := by
  rw [source_trieWalk_branch_advance,evaluateHOLFiniteState_seq_line780] at run
  cases assigned : evaluateHOLFiniteState state (.assign .local (ofString "node") trieWalkBranchNodeExpression) with
  | mk result middle =>
    rw [assigned] at run
    cases result with
    | none =>
      obtain ⟨value,evaluated,selected⟩ := evaluate_local_assign_normal_value state middle (ofString "node") trieWalkBranchNodeExpression assigned
      rw [source_trieWalk_branch_node_expression] at evaluated
      obtain ⟨pointer,child,pointerEval,accessible,memory,word⟩ := eval_load_one_read state trieWalkBranchChildAddressExpression value evaluated
      cases byteRun : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
          (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + index) with
      | none =>
        simp [trieWalkBranchChildAddressExpression,evalHOLExact,evalListHOLExact,nodeLocal,nibsLocal,posLocal,
          wordOpHOL,wordOp,valueIsWord,valueWord,byteRun] at pointerEval
      | some byte =>
        have actual := eval_trieWalk_branch_child_address state node nibs index byte nodeLocal nibsLocal posLocal byteRun
        have equal : pointer = branchChildAddress node byte.toNat :=
          HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (pointerEval.symm.trans actual)))
        subst pointer
        change evaluateHOLFiniteState middle (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.const 1])) = (none,post) at run
        obtain ⟨nextValue,_,advanced⟩ := evaluate_local_assign_normal_value middle post (ofString "pos") _ run
        refine ⟨byte,child,rfl,accessible,memory,?_⟩
        rw [advanced,selected,word]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pos" ≠ ofString "node" from by decide]
    | some result => cases run

theorem evaluate_trieWalk_branch_child_address {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    ∃ byte : UInt8, ∃ child : BitVec 64,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + index) = some byte ∧
      state.memaddrs (branchChildAddress node byte.toNat) ∧
      state.memory (branchChildAddress node byte.toNat) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) :=
  evaluate_trieWalk_branch_advance_child_address state post node nibs index nodeLocal nibsLocal posLocal
    (evaluate_trieWalk_branch_normal_advance state post run)

#print axioms source_trieWalk_branch_node_expression
#print axioms eval_trieWalk_branch_child_address
#print axioms evaluate_trieWalk_branch_advance_child_address
#print axioms evaluate_trieWalk_branch_child_address
end InitECandidate.Runtime

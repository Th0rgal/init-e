import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def InterpreterFundingFrame.mergedError (parent child : InterpreterFundingFrame) : InterpreterFundingFrame :=
 {parent with gas:=parent.gas.mergeError child.gas,stateGas:=parent.stateGas+child.stateGas}
/-- Real failed-child incorporation pops a physical funding entry without
minting funding or losing consumed gas; every other ancestor and input word stays. -/
theorem interpreter_funding_merge_error_body {F : Type} (s : PanSemStateFiniteExact 64 F)
 (lower upper : Nat) (child parent : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s lower upper (child::parent::ancestors))
 (atParent : s.globals.lookup (ofString "ev")=some (.val (.word parent.address)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child.address))) :
 ∃post,evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_incorporate_child_on_error)=(some (.returned (.val (.word 0))),post) ∧
 InterpreterFundingLayout post lower upper (parent.mergedError child::ancestors) ∧
 interpreterFundingUsed (parent.mergedError child::ancestors)=interpreterFundingUsed (child::parent::ancestors) ∧
 post.globals=s.globals ∧post.clock=s.clock ∧
 (∀watched : BitVec 64,upper≤watched.toNat→post.memory watched=s.memory watched) := by
 have childAt:=layout.records child (by simp)
 have parentAt:=layout.records parent (by simp)
 have separate : interpreterFundingDisjoint child parent := (List.pairwise_cons.mp layout.disjoint).1 parent (by simp)
 have pairBudget : parent.gas.potential+child.gas.potential≤200000000 := by
  have budget:=layout.budget
  change child.gas.potential+(parent.gas.potential+interpreterFundingPotential ancestors)≤200000000 at budget
  omega
 let post:=childErrorPost s parent.address parent.gas.left child.gas.left parent.stateGas child.stateGas parent.gas.used child.gas.used
 have run:=evaluate_childError s parent.address child.address parent.gas.left child.gas.left parent.stateGas child.stateGas parent.gas.used child.gas.used
  atParent atChild
  (by
   intro offset member
   simp at member
   rcases member with rfl|rfl|rfl <;>exact parentAt.readable _ (by simp [interpreterFundingOffsets]))
  (by
   intro offset member
   simp at member
   rcases member with rfl|rfl|rfl <;>exact childAt.readable _ (by simp [interpreterFundingOffsets]))
  parentAt.funding.1 childAt.funding.1 parentAt.stateGasAt childAt.stateGasAt parentAt.funding.2.1 childAt.funding.2.1
  (interpreter_funding_offsets_distinct child parent upper childAt.extent parentAt.extent layout.upperBound separate 72 64 (by decide) (by decide))
  (interpreter_funding_offsets_distinct child parent upper childAt.extent parentAt.extent layout.upperBound separate 184 64 (by decide) (by decide))
  (interpreter_funding_offsets_distinct child parent upper childAt.extent parentAt.extent layout.upperBound separate 184 72 (by decide) (by decide))
 have mergedAt : InterpreterFundingFrameAt post lower upper (parent.mergedError child) := by
  constructor
  · exact parentAt.lowerBound
  · exact parentAt.extent
  · exact parentAt.aligned
  · exact parentAt.readable
  · exact childErrorPost_funding s parent.address parent.stateGas child.stateGas parent.gas child.gas parentAt.funding
  · simp [post,childErrorPost,emptyLocalsHOLFinite,sourceWriteWord,InterpreterFundingFrame.mergedError]
 have olderAt (older : InterpreterFundingFrame) (present : older∈ancestors) :
  InterpreterFundingFrameAt post lower upper older := by
  have valid:=layout.records older (by simp [present])
  have apart : interpreterFundingDisjoint parent older := (List.pairwise_cons.mp (List.pairwise_cons.mp layout.disjoint).2).1 older present
  apply valid.after_frame (post:=post) rfl
  intro offset member
  have small : offset.toNat<280 := by
   simp [interpreterFundingOffsets] at member
   rcases member with rfl|rfl|rfl|rfl <;>decide
  have noTouch (k : BitVec 64) (bound : k.toNat<280) : older.address+offset≠parent.address+k :=
   Ne.symm (interpreter_funding_offsets_distinct parent older upper parentAt.extent valid.extent layout.upperBound apart k offset bound small)
  have ne64 : older.address+offset≠parent.address+64#64 := noTouch 64 (by decide)
  have ne72 : older.address+offset≠parent.address+72#64 := noTouch 72 (by decide)
  have ne184 : older.address+offset≠parent.address+184#64 := noTouch 184 (by decide)
  simp [post,childErrorPost,emptyLocalsHOLFinite,sourceWriteWord,ne64,ne72,ne184]
 refine ⟨post,run,?_,?_,rfl,rfl,?_⟩
 · constructor
   · exact layout.upperBound
   · intro record present
     rcases List.mem_cons.mp present with rfl|older
     · exact mergedAt
     · exact olderAt record older
   · apply List.pairwise_cons.mpr
     constructor
     · intro older present
       exact (List.pairwise_cons.mp (List.pairwise_cons.mp layout.disjoint).2).1 older present
     · exact (List.pairwise_cons.mp (List.pairwise_cons.mp layout.disjoint).2).2
   · have conserved:=parent.gas.mergeError_potential child.gas pairBudget
     have budget:=layout.budget
     change child.gas.potential+(parent.gas.potential+interpreterFundingPotential ancestors)≤200000000 at budget
     change (parent.gas.mergeError child.gas).potential+interpreterFundingPotential ancestors≤200000000
     omega
 · have noWrap : parent.gas.used.toNat+child.gas.used.toNat<2^64 := by
    unfold GasFunding.potential at pairBudget
    omega
   change (parent.gas.used+child.gas.used).toNat+interpreterFundingUsed ancestors=
    child.gas.used.toNat+(parent.gas.used.toNat+interpreterFundingUsed ancestors)
   rw [BitVec.toNat_add,Nat.mod_eq_of_lt noWrap]
   omega
 · intro watched above
   have noTouch (offset : BitVec 64) (small : offset.toNat<280) : watched≠parent.address+offset := by
    intro same
    have natural:=congrArg BitVec.toNat same
    rw [interpreter_funding_offset_natural parent upper parentAt.extent layout.upperBound offset small] at natural
    have extent:=parentAt.extent
    omega
   have ne64 : watched≠parent.address+64#64 := noTouch 64 (by decide)
   have ne72 : watched≠parent.address+72#64 := noTouch 72 (by decide)
   have ne184 : watched≠parent.address+184#64 := noTouch 184 (by decide)
   simp [post,childErrorPost,emptyLocalsHOLFinite,sourceWriteWord,ne64,ne72,ne184]
#print axioms interpreter_funding_merge_error_body
end InitECandidate.Runtime

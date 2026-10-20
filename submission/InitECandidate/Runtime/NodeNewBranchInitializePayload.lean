import InitECandidate.Runtime.NodeNewBranchInitialize
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original branch initializer really zeros both payload words, not just
its sixteen child cells. These words lie in the actual 176-byte zeroed record. -/
theorem node_new_branch_initialize_returned_payload {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (value : ValueHOL 64)
 (ndLocal : s.locals.lookup (ofString "nd")=some (.val (.word pointer)))
 (code : s.code=originalRuntimeCode) (ticks : 177≤s.clock)
 (bounded : pointer.toNat+176≤33806089496) (aligned : pointer.toNat%8=0)
 (wordDomain : ∀offset : Nat,offset<176→s.memaddrs (pointer+BitVec.ofNat 64 offset))
 (byteDomain : ∀offset : Nat,offset<176→s.memaddrs (panByteAlignHOL (pointer+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s nodeNewBranchInitialize=(some (.returned value),post)) :
 post.memory (pointer+160#64)=.word 0 ∧post.memory (pointer+168#64)=.word 0 := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "nd"),.const 176]=some [.val (.word pointer),.val (.word (176#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ndLocal]
 obtain ⟨zeroed,zeroRun,coverage,_,_,_,_,domain,_,locals,_,_⟩:=
  evaluate_memzero_aligned_call_with_frame s _ _ pointer 176 args code ticks bounded aligned wordDomain byteDomain
 have ndZeroed : zeroed.locals.lookup (ofString "nd")=some (.val (.word pointer)):=by rw [locals];exact ndLocal
 have address : @evalHOLExact 64 F _ zeroed.toExact (fun a=>Classical.propDecidable (zeroed.memaddrs a))
  (.op .add [.var .local (ofString "nd"),.const 0])=some (.val (.word pointer)) := by
  simp [evalHOLExact,evalListHOLExact,ndZeroed,wordOpHOL,wordOp,valueIsWord,valueWord]
 have pointerDomain : zeroed.memaddrs pointer:=by rw [domain];simpa using wordDomain 0 (by decide)
 have store:=evaluate_store_word zeroed pointer 3 _ (.const 3) address rfl pointerDomain
 let marked:=sourceWriteWord zeroed pointer 3
 have returned : evaluateHOLFiniteState marked (.return (.var .local (ofString "nd")))=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite marked) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,marked,sourceWriteWord,ndZeroed,shapeOfHOLExact]
 have executed : evaluateHOLFiniteState s nodeNewBranchInitialize=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite marked) := by
  rw [source_nodeNewBranch_initialize]
  exact evaluate_seq_none zeroRun (evaluate_seq_none store returned)
 have same : post=emptyLocalsHOLFinite marked:=(Prod.mk.inj (run.symm.trans executed)).2
 have field (offset : Nat) (member : offset∈([160,168] : List Nat)) :
  post.memory (pointer+BitVec.ofNat 64 offset)=.word 0 := by
  have bounds : 0<offset ∧offset+8≤176 := by simp at member;omega
  have offsetAligned : (pointer.toNat+offset)%8=0 := by simp at member;rcases member with rfl|rfl <;>omega
  have zeroAt:=coverage.word zeroed pointer 176 offset bounds.2 (by omega) offsetAligned
  have natural : (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := by
   rw [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  have separate : pointer+BitVec.ofNat 64 offset≠pointer := by
   intro equal
   have sameNat:=congrArg BitVec.toNat equal
   rw [natural] at sameNat
   omega
  rw [same]
  simpa [marked,sourceWriteWord,emptyLocalsHOLFinite,separate] using zeroAt
 exact ⟨field 160 (by simp),field 168 (by simp)⟩

#print axioms node_new_branch_initialize_returned_payload
end InitECandidate.Runtime

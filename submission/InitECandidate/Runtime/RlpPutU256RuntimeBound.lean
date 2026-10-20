import InitECandidate.Runtime.OriginalRlpPutU256Code
import InitECandidate.Runtime.RlpPutU256EncodeTailBound
import InitECandidate.Runtime.U256ToBeMinReturnedCeiling
import InitECandidate.Runtime.VmFn_heap_mark
import InitECandidate.Runtime.AllocationUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def rlpPutU256AfterTmpCost : Nat := u256ToBeMinSourceCost+1+rlpPutU256BytesTailCost
def rlpPutU256AfterMarkCost : Nat := 1+1+rlpPutU256AfterTmpCost
def rlpPutU256SourceCost : Nat := 0+1+rlpPutU256AfterMarkCost

theorem source_rlp_put_u256_prefix :
 rlpPutU256At 0=.decCall (ofString "mark") .one (ofString "heap_mark") [] (rlpPutU256At 1) ∧
 rlpPutU256At 1=.decCall (ofString "tmp") .one (ofString "alloc") [.const 32] (rlpPutU256At 2) ∧
 rlpPutU256At 2=.decCall (ofString "n") .one (ofString "u256_to_be_min")
  [.var .local (ofString "v"),.var .local (ofString "tmp")] (rlpPutU256At 3) := ⟨rfl,rfl,rfl⟩

theorem rlp_put_u256_after_tmp_bounded {F : Type} (s : PanSemStateFiniteExact 64 F) (temporary : BitVec 64)
 (atTmp : s.locals.lookup (ofString "tmp")=some (.val (.word temporary)))
 (code : s.code=originalRuntimeCode) (budget : rlpPutU256AfterTmpCost≤s.clock) :
 RunBounded s (rlpPutU256At 2) rlpPutU256AfterTmpCost := by
 rw [source_rlp_put_u256_prefix.2.2]
 apply runBounded_checked_declaration s _ _ _ _ _ u256ToBeMinSourceCost rlpPutU256BytesTailCost budget
 intro values body callee shape args lookup
 have bounded:=ProgBounded.bodies_of_fun u256_to_be_min_fun_bounded s code
  (by unfold rlpPutU256AfterTmpCost at budget;omega) values body callee shape lookup
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_to_be_min") _ _ body _ shape values callee
  (by rw [code];exact originalRuntimeCode_u256ToBeMin_lookup) lookup
 subst same
 refine ⟨bounded,?_⟩
 intro value post returned checked remaining
 obtain ⟨length,rfl,small⟩:=u256_to_be_min_returned_ceiling (callEntryStateHOLFinite s callee) post value code returned
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_u256_to_be_min)
 rw [returned] at metadata
 apply rlp_put_u256_encode_tail_bounded (setVarHOLFinite (ofString "n") (.val (.word length)) {post with locals:=s.locals}) temporary length _ _ small (metadata.1.trans code) remaining
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTmp
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem rlp_put_u256_after_mark_bounded : ProgBounded (rlpPutU256At 1) rlpPutU256AfterMarkCost := by
 intro F s code budget
 rw [source_rlp_put_u256_prefix.2.1]
 apply runBounded_checked_declaration s _ _ _ _ _ 1 rlpPutU256AfterTmpCost budget
 intro values body callee shape args lookup
 have allocator : FunBounded (ofString "alloc") 1 := ⟨_,_,_,originalRuntimeCode_allocation_lookup,by
  intro F state installed ticks
  have bound:=evaluate_source_alloc_uniform_bounded state installed ticks
  exact ⟨bound.1,bound.2.1,bound.2.2.1⟩⟩
 have bounded:=ProgBounded.bodies_of_fun allocator s code (by unfold rlpPutU256AfterMarkCost at budget;omega) values body callee shape lookup
 refine ⟨bounded,?_⟩
 intro value post returned checked remaining
 have checkedParts := checked
 simp only [Bool.and_eq_true] at checkedParts
 have actualShape : shapeOfHOLExact value=.one := (shapeEqHOL_eq_true _ _).mp checkedParts.1
 obtain ⟨temporary,rfl⟩:=word_of_shape_one actualShape
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
 rw [returned] at metadata
 exact rlp_put_u256_after_tmp_bounded _ temporary
  (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (metadata.1.trans code) remaining

/-- Complete actual original rlp_put_u256, uniformly including malformed inputs,
argument/shape failures, inaccessible memory and allocator rejection. -/
theorem rlp_put_u256_body_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_rlp_put_u256) rlpPutU256SourceCost := by
 have bounded : ProgBounded (rlpPutU256At 0) (0+1+rlpPutU256AfterMarkCost) := by
  rw [source_rlp_put_u256_prefix.1]
  exact ProgBounded.decCall vmBound_heap_mark _ _ _ rlp_put_u256_after_mark_bounded
 intro F s code budget
 rw [sourceFunctionBody_eq_structural]
 exact bounded s code budget
theorem rlp_put_u256_fun_bounded : FunBounded (ofString "rlp_put_u256") rlpPutU256SourceCost :=
 ⟨_,_,_,originalRuntimeCode_rlpPutU256_lookup,rlp_put_u256_body_bounded⟩
#print axioms rlp_put_u256_fun_bounded
#print axioms rlp_put_u256_after_tmp_bounded
#print axioms rlp_put_u256_after_mark_bounded
#print axioms rlp_put_u256_body_bounded
end InitECandidate.Runtime

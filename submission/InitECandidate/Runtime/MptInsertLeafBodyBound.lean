import InitECandidate.Runtime.MptInsertLeafTailBound
import InitECandidate.Runtime.MemeqDecCall64Bound
import InitECandidate.Runtime.PanDecUniformClockBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Equal-length testing bounds the real memeq by the incoming short key,
without assuming a length invariant for the old leaf. -/
theorem mpt_insert_leaf_compare_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (oldKey newKey oldLength newLength : BitVec 64)
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atNewKey : s.locals.lookup (ofString "rk")=some (.val (.word newKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word oldLength)))
 (atNewLength : s.locals.lookup (ofString "rl")=some (.val (.word newLength)))
 (short : newLength.toNat≤18) (code : s.code=originalRuntimeCode) (budget : 73≤s.clock) :
 RunBounded s
  (.ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
   (.decCall (ofString "eq") .one (ofString "memeq")
    [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")] mptInsertLeafEqualReturn) .skip) 73 := by
 unfold RunBounded
 rw [evaluateHOLFiniteState_ite]
 by_cases same : oldLength=newLength
 · subst oldLength
   have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))=some (.val (.word (1#64))) := by
    simp [evalHOLExact,atOldLength,atNewLength,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard]
   simp only [show ¬(1#64=0) by decide,if_false]
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
    [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]=
    some [.val (.word oldKey),.val (.word newKey),.val (.word newLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atOldKey,atNewKey,atOldLength]
   have bounded:=evaluate_memeq_decCall64_straight_bounded s (ofString "eq") mptInsertLeafEqualReturn
    (by decide) _ _ _ oldKey newKey newLength code args (by omega) (by omega)
   exact ⟨by have := bounded.1;omega,bounded.2.1,bounded.2.2⟩
 · have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))=some (.val (.word (0#64))) := by
    simp [evalHOLExact,atOldLength,atNewLength,Compiler.Encoders.Asm.wordCmpHOL,same]
   rw [guard]
   simp [evaluateHOLFiniteState_skip]

theorem mpt_insert_leaf_loaded_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (oldKey newKey oldLength newLength : BitVec 64)
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atNewKey : s.locals.lookup (ofString "rk")=some (.val (.word newKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word oldLength)))
 (atNewLength : s.locals.lookup (ofString "rl")=some (.val (.word newLength)))
 (short : newLength.toNat≤18) (code : s.code=originalRuntimeCode) (budget : 2^64+200≤s.clock) :
 RunBounded s (mptInsertLeafAt 2) (2^64+200) := by
 have bound : RunBounded s (mptInsertLeafAt 2) (73+(2^64+100)) := by
  rw [source_mpt_insert_leaf_2]
  exact RunBounded.seq
   (mpt_insert_leaf_compare_bounded s oldKey newKey oldLength newLength atOldKey atNewKey atOldLength atNewLength short code (by omega))
   (by omega) (by
    intro next _ nextCode clock
    exact mpt_insert_leaf_split_tail_bounded next (nextCode.trans code) clock)
 exact bound.weaken (by omega)

/-- Whole original leaf insertion for indexed keys of at most18 nibbles.
The actual initial loads either reject or supply checked word values; no
readable old-node memory, old-leaf length, room or callee premise is assumed. -/
theorem mpt_insert_leaf_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (key length : BitVec 64)
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (short : length.toNat≤18) (code : s.code=originalRuntimeCode) (budget : 2^64+200≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn__insert_into_leaf) (2^64+200) := by
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (mptInsertLeafAt 0) (2^64+200)
 rw [source_mpt_insert_leaf_0]
 unfold RunBounded
 apply evaluate_dec_one_uniform_clock_bounded
 intro oldKey
 change RunBounded (setVarHOLFinite (ofString "ek") (.val (.word oldKey)) s) (mptInsertLeafAt 1) (2^64+200)
 rw [source_mpt_insert_leaf_1]
 unfold RunBounded
 apply evaluate_dec_one_uniform_clock_bounded
 intro oldLength
 change RunBounded (setVarHOLFinite (ofString "el") (.val (.word oldLength))
  (setVarHOLFinite (ofString "ek") (.val (.word oldKey)) s)) (mptInsertLeafAt 2) (2^64+200)
 apply mpt_insert_leaf_loaded_bounded _ oldKey key oldLength length
 · simp (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKey
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 · exact short
 · exact code
 · exact budget

#print axioms mpt_insert_leaf_compare_bounded
#print axioms mpt_insert_leaf_body_bounded
end InitECandidate.Runtime

import InitECandidate.Runtime.RlpWordAssignmentCursor
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A normal fixed-byte encoder assignment returns an advance inside the fence.
 Missing or malformed source operands cannot satisfy the actual normal-run premise. -/
theorem rlp_bytes_assignment_returns_cursor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (cursor resultName : MlS) (expression : ExpHOL 64) (pointer length : BitVec 64) (DF : Nat)
 (different : resultName≠cursor)
 (atCursor : s.locals.lookup cursor=some (.val (.word pointer)))
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,resultName),none)) (ofString "rlp_encode_bytes")
  [.var .local cursor,expression,.const length])=(none,post)) :
 ∃written : BitVec 64,post.locals.lookup resultName=some (.val (.word written)) ∧
  post.locals.lookup cursor=some (.val (.word pointer)) ∧pointer.toNat+written.toNat≤DF+8 := by
 obtain ⟨values,body,callee,shape,args,lookup⟩:=rlp_assignment_call_normal_lookup s post resultName (ofString "rlp_encode_bytes") _ run
 have installed : s.code.lookup (ofString "rlp_encode_bytes")=
  some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_bytes,.one) := by
  rw [code];exact originalRuntimeCode_rlpEncodeBytes_lookup
 obtain ⟨first,rest,rfl,evalFirst,evalRest⟩:=evalList_cons' s _ _ _ args
 obtain ⟨second,rest2,rfl,evalSecond,evalRest2⟩:=evalList_cons' s _ _ _ evalRest
 obtain ⟨third,rest3,rfl,evalThird,evalNil⟩:=evalList_cons' s _ _ _ evalRest2
 have empty:=evalList_nil' s _ evalNil
 subst empty
 have firstEq : first=.val (.word pointer) := by
  simp [EV,evalHOLExact,atCursor] at evalFirst
  exact evalFirst.symm
 subst firstEq
 have thirdEq : third=.val (.word length) := by
  simp [EV,evalHOLExact] at evalThird
  exact evalThird.symm
 subst thirdEq
 have originalLookup:=lookup
 rw [code] at originalLookup
 have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeBytes_lookup originalLookup
 simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true] at shapes
 have secondShape : shapeEqHOL .one (shapeOfHOLExact second)=true := by
  simpa [shapeOfHOLExact,shapeEqHOL] using shapes
 obtain ⟨source,rfl⟩:=scalar_of_shape secondShape
 have actualLookup:=pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
  (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) pointer source length (by decide) (by decide) (by decide) installed
 rw [actualLookup] at lookup
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj lookup |>.symm
 obtain ⟨value,bodyPost,returned,postEq⟩:=assignment_call_normal_context s post .local resultName (ofString "rlp_encode_bytes")
  [.var .local cursor,expression,.const length] _ _ _ _ args actualLookup run
 have result:=rlp_encode_bytes_returned_cursor (callEntryStateHOLFinite s
   (((HolFiniteMapExact.empty.update (ofString "dst",.val (.word pointer))).update (ofString "src",.val (.word source))).update (ofString "n",.val (.word length))))
  bodyPost pointer length value DF code fence cap lower upper
  (by simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) returned
 obtain ⟨written,rfl,fits⟩:=result
 refine ⟨written,?_,?_,fits⟩
 · rw [postEq]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · rw [postEq]
   simpa [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using atCursor
#print axioms rlp_bytes_assignment_returns_cursor
end InitECandidate.Runtime

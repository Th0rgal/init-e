import InitECandidate.Runtime.RlpEncodingReturnedCursor
import InitECandidate.Runtime.PanAssignmentCallNormalContext
import InitECandidate.Runtime.RecDecompGD
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A normal actual assignment call necessarily evaluated and bound its arguments. -/
theorem rlp_assignment_call_normal_lookup {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function : MlS) (arguments : List (ExpHOL 64))
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) function arguments)=(none,post)) :
 ∃values body callee shape,
  evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values ∧
  lookupCodeHOLFinite s.code.lookup function values=some (body,callee,shape) := by
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>rw [evaluateHOLFiniteState_call,args] at run;cases run
 | some values=>
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none=>rw [evaluateHOLFiniteState_call,args] at run;dsimp only at run;rw [lookup] at run;cases run
  | some data=>obtain ⟨body,callee,shape⟩:=data;exact ⟨values,body,callee,shape,rfl,lookup⟩

/-- A normal scalar-encoding assignment returns a bounded cursor advance.
 The value expression is arbitrary: failures are excluded only by the actual normal run. -/
theorem rlp_word_assignment_returns_cursor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (cursor resultName : MlS) (expression : ExpHOL 64) (pointer : BitVec 64) (DF : Nat)
 (different : resultName≠cursor)
 (atCursor : s.locals.lookup cursor=some (.val (.word pointer)))
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,resultName),none)) (ofString "rlp_encode_word")
  [.var .local cursor,expression])=(none,post)) :
 ∃written : BitVec 64,post.locals.lookup resultName=some (.val (.word written)) ∧
  post.locals.lookup cursor=some (.val (.word pointer)) ∧1≤written.toNat ∧written.toNat≤9 ∧
  pointer.toNat+written.toNat≤DF+8 := by
 obtain ⟨values,body,callee,shape,args,lookup⟩:=rlp_assignment_call_normal_lookup s post resultName (ofString "rlp_encode_word") _ run
 have installed : s.code.lookup (ofString "rlp_encode_word")=
  some ([(ofString "dst",.one),(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,.one) := by
  rw [code];exact originalRuntimeCode_rlpEncodeWord_lookup
 obtain ⟨first,rest,rfl,evalFirst,evalRest⟩:=evalList_cons' s _ _ _ args
 obtain ⟨second,rest2,rfl,evalSecond,evalNil⟩:=evalList_cons' s _ _ _ evalRest
 have empty:=evalList_nil' s _ evalNil
 subst empty
 have firstEq : first=.val (.word pointer) := by
  simp [EV,evalHOLExact,atCursor] at evalFirst
  exact evalFirst.symm
 subst firstEq
 have originalLookup:=lookup
 rw [code] at originalLookup
 have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeWord_lookup originalLookup
 simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true] at shapes
 have secondShape : shapeEqHOL .one (shapeOfHOLExact second)=true := by
  simpa [shapeOfHOLExact,shapeEqHOL] using shapes
 obtain ⟨input,rfl⟩:=scalar_of_shape secondShape
 have actualLookup:=pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word") (ofString "dst") (ofString "w")
  (sourceFunctionBody Guest.guestFn_rlp_encode_word) pointer input (by decide) installed
 rw [actualLookup] at lookup
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj lookup |>.symm
 obtain ⟨value,bodyPost,returned,postEq⟩:=assignment_call_normal_context s post .local resultName (ofString "rlp_encode_word")
  [.var .local cursor,expression] _ _ _ _ args actualLookup run
 have result:=rlp_encode_word_returned_cursor (callEntryStateHOLFinite s
   ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word pointer))).update (ofString "w",.val (.word input))))
  bodyPost pointer input value DF code fence cap lower upper
  (by simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) returned
 obtain ⟨written,rfl,positive,small,fits⟩:=result
 refine ⟨written,?_,?_,positive,small,fits⟩
 · rw [postEq]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · rw [postEq]
   simpa [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using atCursor
#print axioms rlp_assignment_call_normal_lookup
#print axioms rlp_word_assignment_returns_cursor
end InitECandidate.Runtime

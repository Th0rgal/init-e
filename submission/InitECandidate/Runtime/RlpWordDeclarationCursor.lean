import InitECandidate.Runtime.RlpEncodingReturnedCursor
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A completed actual RLP declaration exposes a one-to-nine-byte key to
its continuation. The size follows from the installed writer body, at the
same actual clock; no writer-return or continuation contract is assumed. -/
theorem rlp_word_declaration_returned_cursor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer input : BitVec 64) (value : ValueHOL 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word pointer),.val (.word input)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "rlp_encode_word") arguments tail)=
  (some (.returned value),post)) :
 ∃written : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
  1≤written.toNat ∧written.toNat≤9 ∧pointer.toNat+written.toNat≤DF+8 ∧
  evaluateHOLFiniteState (setVarHOLFinite name (.val (.word written)) {bodyPost with locals:=s.locals}) tail=
   (some (.returned value),output) ∧
  post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 have installed : s.code.lookup (ofString "rlp_encode_word")=some
  ([(ofString "dst",.one),(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,.one) := by
  rw [code];exact originalRuntimeCode_rlpEncodeWord_lookup
 have lookup:=pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word") (ofString "dst") (ofString "w")
  (sourceFunctionBody Guest.guestFn_rlp_encode_word) pointer input (by decide) installed
 obtain ⟨encoded,bodyPost,output,bodyRun,_,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope
  s post name (ofString "rlp_encode_word") .one .one arguments _ _ tail _ value args lookup run
 have returned:=rlp_encode_word_returned_cursor (callEntryStateHOLFinite s
  ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word pointer))).update (ofString "w",.val (.word input))))
  bodyPost pointer input encoded DF code fence cap lower upper
  (by simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
 obtain ⟨written,rfl,positive,short,fits⟩:=returned
 exact ⟨written,bodyPost,output,positive,short,fits,tailRun,postEq⟩

#print axioms rlp_word_declaration_returned_cursor
end InitECandidate.Runtime

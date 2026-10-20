import InitECandidate.Runtime.RlpWordDeclarationCursor
import InitECandidate.Runtime.RlpWritersRuntimeBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RlpWordReturnedUpperFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def RlpWordDeclarationReady {F : Type} (base next : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer : BitVec 64) (DF : Nat) : Prop :=
 ∃written : BitVec 64,next.locals.lookup name=some (.val (.word written)) ∧
  1≤written.toNat ∧written.toNat≤9 ∧pointer.toNat+written.toNat≤DF+8 ∧
  (∀key,key≠name→next.locals.lookup key=base.locals.lookup key) ∧
  next.code=base.code ∧next.memaddrs=base.memaddrs ∧next.be=base.be ∧
  next.globals=base.globals ∧
  (∀watched : BitVec 64,pointer.toNat+9≤watched.toNat→next.memory watched=base.memory watched)

/-- The actual scalar writer reaches its continuation with a short encoded
length, or terminates within the uniform writer ceiling. This covers write
errors as well as normal returns. -/
theorem rlp_word_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer input : BitVec 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word pointer),.val (.word input)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (budget : rlpWriterSourceCost+1≤s.clock) :
 Reaches s (.decCall name .one (ofString "rlp_encode_word") arguments tail)
  (fun next=>RlpWordDeclarationReady s next name pointer DF) (rlpWriterSourceCost+1) tail := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (HolFiniteMapExact.empty.update (ofString "dst",.val (.word pointer))).update (ofString "w",.val (.word input))
 let entry:=callEntryStateHOLFinite s callee
 have installed : s.code.lookup (ofString "rlp_encode_word")=some
  ([(ofString "dst",.one),(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,.one) := by
  rw [code];exact originalRuntimeCode_rlpEncodeWord_lookup
 have lookup:=pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word") (ofString "dst") (ofString "w")
  (sourceFunctionBody Guest.guestFn_rlp_encode_word) pointer input (by decide) installed
 have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_rlp_encode_word) rlpWriterSourceCost :=
  rlp_encode_word_body_bounded entry code (by change rlpWriterSourceCost≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "rlp_encode_word") .one .one arguments _ _ tail callee
  rlpWriterSourceCost _ args lookup budget bounded
 intro value post run checked
 have returned:=rlp_encode_word_returned_cursor entry post pointer input value DF code fence cap lower upper
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) run
 obtain ⟨written,rfl,positive,short,fits⟩:=returned
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_encode_word)
 rw [run] at metadata
 have frame:=rlp_word_returned_upper_frame entry post pointer input (.val (.word written)) DF code fence cap
  (by omega)
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) run
 refine ⟨written,?_,positive,short,fits,?_,metadata.1,metadata.2.1,metadata.2.2.1,frame.1,frame.2⟩
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms rlp_word_declaration_reaches
end InitECandidate.Runtime

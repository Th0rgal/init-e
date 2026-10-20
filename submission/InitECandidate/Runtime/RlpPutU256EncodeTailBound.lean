import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.RlpPutU256CheckedDeclaration
import InitECandidate.Runtime.RlpEncodeBytesCallBound
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.RecDecompGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def rlpPutU256At (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_rlp_put_u256)
def rlpPutU256EncodeCost : Nat := rlpEncodeBytesSourceCost (2^61)
def rlpPutU256BytesTailCost : Nat := rlpPutU256EncodeCost+1+1

theorem source_rlp_put_u256_encode : rlpPutU256At 3=
 .decCall (ofString "w") .one (ofString "rlp_encode_bytes")
  [.var .local (ofString "dst"),.var .local (ofString "tmp"),.var .local (ofString "n")]
  (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
   (.return (.var .local (ofString "w")))) := rfl

theorem rlp_put_u256_encode_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (temporary length : BitVec 64)
 (atTmp : s.locals.lookup (ofString "tmp")=some (.val (.word temporary)))
 (atLen : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (small : length.toNat<2^61) (code : s.code=originalRuntimeCode)
 (budget : rlpPutU256BytesTailCost≤s.clock) : RunBounded s (rlpPutU256At 3) rlpPutU256BytesTailCost := by
 rw [source_rlp_put_u256_encode]
 apply runBounded_checked_declaration s _ _ _ _ _ rlpPutU256EncodeCost 1 budget
 intro values body callee returnShape args lookup
 cases dst : s.locals.lookup (ofString "dst") with
 | none=>simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,dst] at args
 | some held=>
  have arguments : values=[held,.val (.word temporary),.val (.word length)] := by
   simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,dst,atTmp,atLen] at args
   exact args.symm
  subst values
  rw [code] at lookup
  cases held with
  | val output=>
   cases output with
   | word output=>
    have realLookup:=pan_three_word_lookup originalRuntimeCode.lookup (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
     (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) output temporary length (by decide) (by decide) (by decide) originalRuntimeCode_rlpEncodeBytes_lookup
    rw [realLookup] at lookup
    obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj lookup |>.symm
    have cost : rlpEncodeBytesSourceCost length.toNat≤rlpPutU256EncodeCost := by
     unfold rlpPutU256EncodeCost rlpEncodeBytesSourceCost
     omega
    let bindings : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word output))).update (ofString "src",.val (.word temporary))).update (ofString "n",.val (.word length))
    have bound:=rlp_encode_bytes_body_bounded (callEntryStateHOLFinite s bindings) output temporary length
     (by simp (config:={decide:=true}) [bindings,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
     (by simp (config:={decide:=true}) [bindings,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
     (by simp [bindings,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) code (by omega)
     (by change rlpEncodeBytesSourceCost length.toNat≤s.clock-1;unfold rlpPutU256BytesTailCost at budget;omega)
    refine ⟨RunBounded.weaken bound cost,?_⟩
    intro value post returned checked ticks
    have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s bindings) (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
    rw [returned] at metadata
    have tail : ProgBounded (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
     (.return (.var .local (ofString "w")))) (0+1+0) := ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ rfl)
    exact tail _ (metadata.1.trans code) ticks
  | rStruct fields=>
   have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeBytes_lookup lookup
   simp [List.zip,List.zipWith,shapeEqHOL,shapeOfHOLExact] at shapes
  | nStruct name fields=>
   have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeBytes_lookup lookup
   simp [List.zip,List.zipWith,shapeEqHOL,shapeOfHOLExact] at shapes
#print axioms rlp_put_u256_encode_tail_bounded
end InitECandidate.Runtime

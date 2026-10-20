import InitECandidate.Runtime.EncodeHeaderActualPrefixPlan
import InitECandidate.Runtime.RlpPutU256CheckedDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def encodeHeaderFirstWriterCost : Nat := rlpEncodeBytesSourceCost 32+1+encodeHeaderActualPrefixPlanCost
/-- The original first declared writer establishes w from its real return,
then its real increment enters the checked concrete writer plan. -/
theorem encode_header_first_writer_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (small : length.toNat≤2^62) (budget : encodeHeaderFirstWriterCost≤s.clock) :
 RunBounded s (encodeHeaderAt 2) encodeHeaderFirstWriterCost := by
 have stage : encodeHeaderAt 2=.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
  [.var .local (ofString "p"),encodeHeaderPrefixField 8,.const 32] (encodeHeaderAt 3) := rfl
 rw [stage]
 apply runBounded_checked_declaration s _ _ _ _ _ (rlpEncodeBytesSourceCost 32) encodeHeaderActualPrefixPlanCost budget
 intro values body callee shape args lookup
 obtain ⟨dst,atP,low,high⟩:=valid.cursor
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (encodeHeaderPrefixField 8) with
 | none=>
  simp only [evalListHOLFinite_eq_toExact,evalListHOLExact] at args
  rw [evaluated] at args
  simp at args
 | some input=>
  have actual : values=[.val (.word dst),input,.val (.word (32#64))] := by
   simp only [evalListHOLFinite_eq_toExact,evalListHOLExact] at args
   rw [evaluated] at args
   simp [evalHOLExact,atP] at args
   exact args.symm
  subst values
  have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_bytes") _ _ body _ shape _ callee
   (by rw [valid.code];exact originalRuntimeCode_rlpEncodeBytes_lookup) lookup
  subst same
  rw [valid.code] at lookup
  have bindings:=callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
  cases input with
  | rStruct fields=>
   have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeBytes_lookup lookup
   simp [List.zip,List.zipWith,shapeEqHOL,shapeOfHOLExact] at shapes
  | nStruct name fields=>
   have shapes:=lookupCode_shapes originalRuntimeCode_rlpEncodeBytes_lookup lookup
   simp [List.zip,List.zipWith,shapeEqHOL,shapeOfHOLExact] at shapes
  | val held=>
   cases held with
   | word src=>
    let entry:=callEntryStateHOLFinite s callee
    have atDst : entry.locals.lookup (ofString "dst")=some (.val (.word dst)) := by
     simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
    have atSrc : entry.locals.lookup (ofString "src")=some (.val (.word src)) := by
     simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
    have atLen : entry.locals.lookup (ofString "n")=some (.val (.word (32#64))) := by
     simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
    have bounded:=rlp_encode_bytes_body_bounded entry dst src 32 atDst atSrc atLen valid.code (by decide)
     (by change rlpEncodeBytesSourceCost 32≤s.clock-1;unfold encodeHeaderFirstWriterCost at budget;omega)
    refine ⟨bounded,?_⟩
    intro value post returned _ remaining
    have framed:=encode_header_bytes_body_returned_frame entry post dst 32 lo (header+136) DF value
     valid.code valid.fence cap aligned below low high atDst atLen returned
    obtain ⟨written,rfl,fits⟩:=framed.1
    let ready:=setVarHOLFinite (ofString "w") (.val (.word written)) {post with locals:=s.locals}
    have readyP : ready.locals.lookup (ofString "p")=some (.val (.word dst)) := by
     simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atP
    have readyW : ready.locals.lookup (ofString "w")=some (.val (.word written)) := by
     simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have increment:=encode_header_cursor_increment ready dst written DF cap readyP readyW fits
    have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
    rw [returned] at metadata
    have nextValid : EncodeHeaderPrefixInvariant
      (setVarHOLFinite (ofString "p") (.val (.word (dst+written))) ready) header heap lo (header+136) length DF := by
     constructor
     · exact metadata.1.trans valid.code
     · change Fence post.memaddrs DF;rw [metadata.2.1];exact valid.fence
     · simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using valid.atH
     · change post.globals.lookup (ofString "heap_ptr")=_;rw [framed.2.2];exact valid.atHeap
     · change post.memory (header+136)=_;rw [framed.2.1];exact valid.atLength
     · refine ⟨dst+written,?_,?_,?_⟩
       · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
       · rw [increment.2];omega
       · rw [increment.2];exact fits
    have stage3 : encodeHeaderAt 3=.seq encodeHeaderPrefixIncrement (encodeHeaderAt 4) := rfl
    rw [stage3]
    have advanced : RunBounded ready encodeHeaderPrefixIncrement 0 :=
     ProgBounded.straight _ (by decide_cbv) ready (metadata.1.trans valid.code) (Nat.zero_le _)
    have whole:=RunBounded.seq advanced (b:=encodeHeaderActualPrefixPlanCost) (by change 0+encodeHeaderActualPrefixPlanCost≤post.clock;simpa only [Nat.zero_add] using remaining) (by
     intro next nextRun _ ticks
     dsimp only [encodeHeaderPrefixIncrement] at nextRun
     rw [increment.1] at nextRun
     have equal:=(Prod.mk.inj nextRun).2
     subst next
     exact encode_header_actual_prefix_plan_bounded _ header heap lo length DF nextValid cap heapCap heapFence aligned below loHeap small ticks)
    simpa only [Nat.zero_add] using whole
#print axioms encode_header_first_writer_bounded
end InitECandidate.Runtime

import InitECandidate.Runtime.EncWriters2GD
import InitECandidate.Runtime.OriginalEncodeCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual scalar writer: returned cursor and old-cell/global frame together. -/
theorem encode_header_word_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst input lo watched : BitVec 64) (DF : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atInput : s.locals.lookup (ofString "w")=some (.val (.word input)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_word)=(some (.returned value),post)) :
 WRet DF dst value ∧post.memory watched=s.memory watched ∧post.globals=s.globals := by
 have spec:=encodeWord_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched) fence lo aligned below dst input dstLow (by omega)
 have dom : DomD s.memaddrs s.be s := ⟨(by intro a ha;have h:=fence a ha;omega),rfl,rfl⟩
 have facts:=spec F s code dom trivial (by intro name impossible;exact impossible.elim) s.globals rfl ⟨atDst,atInput⟩
 obtain ⟨_,_,cursor⟩:=facts.2.2.2.1 value (by rw [run])
 have kept:=evaluate_keepsGA goodGA goodGA_bodies (sourceFunctionBody Guest.guestFn_rlp_encode_word)
  (keepsGA_of_installed originalRuntimeCode_rlpEncodeWord_lookup (by decide)) s code
 rw [run] at facts kept
 exact ⟨wret_of_hdr cursor,facts.1,kept⟩
/-- Actual byte writer: returned cursor and old-cell/global frame together. -/
theorem encode_header_bytes_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst length lo watched : BitVec 64) (DF : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)=(some (.returned value),post)) :
 WRet DF dst value ∧post.memory watched=s.memory watched ∧post.globals=s.globals := by
 have spec:=encodeBytes_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched) fence cap lo aligned below dst length dstLow (by omega)
 have dom : DomD s.memaddrs s.be s := ⟨(by intro a ha;have h:=fence a ha;omega),rfl,rfl⟩
 have facts:=spec F s code dom trivial (by intro name impossible;exact impossible.elim) s.globals rfl ⟨atDst,atLength⟩
 obtain ⟨_,_,cursor⟩:=facts.2.2.2.1 value (by rw [run])
 have kept:=evaluate_keepsGA goodGA goodGA_bodies (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
  (keepsGA_of_installed originalRuntimeCode_rlpEncodeBytes_lookup (by decide)) s code
 rw [run] at facts kept
 exact ⟨cursor,facts.1,kept⟩
#print axioms encode_header_word_body_returned_frame
#print axioms encode_header_bytes_body_returned_frame
end InitECandidate.Runtime

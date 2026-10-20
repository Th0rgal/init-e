import InitECandidate.Runtime.RlpWordUpperFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual scalar writer preserves every memory word beyond its nine
output bytes and all globals. This uses the same actual returned execution,
without a minimum-clock or successful-store premise. -/
theorem rlp_word_returned_upper_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer input : BitVec 64) (value : ValueHOL 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (fits : pointer.toNat+16<2^64)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word pointer)))
 (atInput : s.locals.lookup (ofString "w")=some (.val (.word input)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_word)=
  (some (.returned value),post)) :
 post.globals=s.globals ∧
  (∀watched : BitVec 64,pointer.toNat+9≤watched.toNat→post.memory watched=s.memory watched) := by
 have kept:=evaluate_keepsGA goodGA goodGA_bodies (sourceFunctionBody Guest.guestFn_rlp_encode_word)
  (keepsGA_of_installed originalRuntimeCode_rlpEncodeWord_lookup (by decide)) s code
 rw [run] at kept
 refine ⟨kept,?_⟩
 intro watched beyond
 have spec:=encodeWord_upper_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched)
  fence pointer input fits beyond
 have dom : DomD s.memaddrs s.be s :=
  ⟨(by intro address present;have bound:=fence address present;omega),rfl,rfl⟩
 have actual:=spec F s code dom trivial (by intro name impossible;exact impossible.elim)
  s.globals rfl ⟨atDst,atInput⟩
 rw [run] at actual
 exact actual.1

#print axioms rlp_word_returned_upper_frame
end InitECandidate.Runtime

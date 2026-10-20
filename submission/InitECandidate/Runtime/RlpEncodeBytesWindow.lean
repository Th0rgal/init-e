import InitECandidate.Runtime.RlpEncodeBytesTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- **The actual `rlp_encode_bytes`.**  The single-byte prefix handles the one-byte string, then the
actual `rlp_write_header` writes the header at `dst` and the actual `memcpy` copies the `n` source
bytes behind it.  The header is at most nine bytes, so every word outside the `9 + n` byte window at
`dst` keeps its cell. -/
theorem rlpEncodeBytes_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D S N w : BitVec 64) (out : ¬ MWin D (9 + N.toNat) w)
    (small : N.toNat + 32 < 2 ^ 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hs : s.locals.lookup (ofString "src") = some (.val (.word S)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)).2.memory w =
      s.memory w := by
  rw [source_rlpEncodeBytes_body]
  rw [evaluateHOLFiniteState_seq_line780]
  cases pRun : evaluateHOLFiniteState s rlpEncodeBytesPrefix with
  | mk rp mid =>
    cases rp with
    | some res =>
      have hw := rlpEncodeBytesPrefix_window s D w (mwin_mono (by omega) out) hd
      rw [pRun] at hw
      exact hw
    | none =>
      obtain ⟨hmem,hcode,hglob,hlook⟩ := rlpEncodeBytesPrefix_none s mid pRun
      have hd' : mid.locals.lookup (ofString "dst") = some (.val (.word D)) :=
        (hlook (ofString "dst") (by decide)).trans hd
      have hs' : mid.locals.lookup (ofString "src") = some (.val (.word S)) :=
        (hlook (ofString "src") (by decide)).trans hs
      have hn' : mid.locals.lookup (ofString "n") = some (.val (.word N)) :=
        (hlook (ofString "n") (by decide)).trans hn
      exact (rlpEncodeBytesTail_window mid D S N w out small hd' hs' hn'
        (hcode.trans code)).trans (congrFun hmem w)

#print axioms rlpEncodeBytes_window

end InitECandidate.Runtime

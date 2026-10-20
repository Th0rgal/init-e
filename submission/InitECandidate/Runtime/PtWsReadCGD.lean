import InitECandidate.Runtime.PtBalCallsGD
/-!
OPEN intermediate contract (explicit, never an assumption of the final bound): frames of the two witness readers
`ws_get_account_optional(addr)` and `ws_get_storage(addr, key)`.

Their actual writes: fresh heap (`alloc` of key-hash buffers, decoded nodes and accounts; `heap_mark`/`heap_release`
around the trie lookups), the keccak state buffers (`keccak_st`/`keccak_pad`), and the witness storage-trie cache
`ws + 32` (`htab_set`, which may also relocate its arrays into fresh heap); `decode_witness_to_mpt` stores into the
node it returns. Exceptions: `mpt_fail` (MptErr), RLP errors (RlpErr), `throw StateErr` in `ws_get_storage`.

`WsReadC D B A WsI f body`: from any state where the witness invariant `WsI M H Ow` holds (heap `H`, witness-owned
region `Ow`: keccak buffers, the cache table, the witness node arena), every outcome of the body (normal, returned,
raised, timed out) keeps every word below `H` outside `Ow`; a returned run leaves the non-heap globals unchanged, the
heap at `H' ≥ H`, memory below `H` outside `Ow` unchanged, and `WsI` re-established at `H'` with owned region inside
`Ow ∪ [H, H')`. `WsIFrame WsI`: the witness invariant survives writes outside its owned region and heap growth, and
its owned region lies below the heap.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Non-heap globals equal. -/
def GlobNH (G G' : GA) : Prop := ∀ g, g ≠ ofString "heap_ptr" → G'.lookup g = G.lookup g

/-- The witness-reader frame contract for the body of one reader (see the module doc). -/
def WsReadC (D : BitVec 64 → Prop) (B : Bool) (A : GA → Prop)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (LPe : GA → Prop) (RV : ValueHOL 64 → Prop)
    (body : ProgHOL 64) : Prop :=
  ∀ (w : BitVec 64) (M1 : Mem) (G1 : GA) (H : BitVec 64) (Ow : BitVec 64 → Prop),
    WsI M1 H Ow → HeapIs G1 H → ¬ Ow w → w.toNat < H.toNat →
    AQGD D B A w (fun _ => False) (fun L M G => LPe L ∧ M = M1 ∧ G = G1) (fun _ _ _ => True)
      (fun v M G => ∃ (H' : BitVec 64) (Ow' : BitVec 64 → Prop), HeapIs G H' ∧ H.toNat ≤ H'.toNat ∧ GlobNH G1 G ∧
        WsI M H' Ow' ∧ (∀ x, Ow' x → Ow x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
        (∀ x, x.toNat < H.toNat → ¬ Ow x → M x = M1 x) ∧ RV v) body

/-- The witness invariant survives writes outside its owned region and heap growth; its owned region lies below the
heap (the witness globals `ws`, `keccak_st`, `keccak_pad`, `mpt_nib_scratch`, `empty_trie_root` are pinned by the
arena). -/
def WsIFrame (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) : Prop :=
  (∀ M H Ow M' H', WsI M H Ow → (∀ x, Ow x → M' x = M x) → H.toNat ≤ H'.toNat → WsI M' H' Ow) ∧
    ∀ M H Ow, WsI M H Ow → ∀ x, Ow x → x.toNat < H.toNat

/-- The open witness-reader obligations used by the block-access-list builder. -/
def WsReadObl (D : BitVec 64 → Prop) (B : Bool) (A : GA → Prop)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) : Prop :=
  WsIFrame WsI ∧
  (∀ Ad : BitVec 64, WsReadC D B A WsI (fun L => L.lookup (ofString "addr") = some (.val (.word Ad)))
    (fun v => ∃ y : BitVec 64, v = .val (.word y)) (sourceFunctionBody Guest.guestFn_ws_get_account_optional)) ∧
  (∀ Ad Ky : BitVec 64, WsReadC D B A WsI (fun L => L.lookup (ofString "addr") = some (.val (.word Ad)) ∧
    L.lookup (ofString "key") = some (.val (.word Ky)))
    (fun v => ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)])
    (sourceFunctionBody Guest.guestFn_ws_get_storage))

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.balStep_trans

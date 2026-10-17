import InitECandidate.Runtime.HashSelect32
import InitECandidate.Runtime.HashExpressionTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashLoadLE32 (offset : Nat) : ExpHOL 64 :=
  let address (extra : BitVec 64) := .op .add
    [.var .local (ofString "p"),.const (BitVec.ofNat 64 offset),.const extra]
  .op .or [.loadByte (memeqAddress (ofString "p") offset),
    .shift .lsl (.loadByte (address 1)) (.const 8),
    .shift .lsl (.loadByte (address 2)) (.const 16),
    .shift .lsl (.loadByte (address 3)) (.const 24)]

def hashFast52 : ProgHOL 64 :=
  match hashAfter32 with | .ite _ body _ => body | _ => .skip

theorem source_hash_fast20 : hashFast20 =
    hashWordThen 0 (hashWordThen 8 (hashExpressionTail (hashLoadLE32 16))) := by rfl

theorem source_hash_fast52 : hashFast52 =
    hashWordThen 0 (hashWordThen 8 (hashWordThen 16 (hashWordThen 24
      (hashWordThen 32 (hashWordThen 40 (hashExpressionTail (hashLoadLE32 48))))))) := by rfl

#print axioms source_hash_fast20
#print axioms source_hash_fast52
end InitECandidate.Runtime

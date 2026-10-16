import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_hash with | .function fn => fn.body | _ => .skip

def hashAlignedBody : ProgHOL 64 :=
  match hashDecodedBody with | .dec _ _ _ (.dec _ _ _ (.seq (.ite _ body _) _)) => body | _ => .skip

def hashFast32 : ProgHOL 64 :=
  match hashAlignedBody with | .seq _ (.seq (.ite _ body _) _) => body | _ => .skip

def hashWordThen (offset : Nat) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "w") (.load .one (memeqAddress (ofString "p") offset)))
    (.seq (.assign .local (ofString "h") (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")])) continuation)

def hashFinish : ProgHOL 64 :=
  .seq (.assign .local (ofString "h") (.op .xor [.var .local (ofString "h"),
      .shift .lsr (.var .local (ofString "h")) (.const 32)]))
    (.seq (.assign .local (ofString "h") (.panop .mul [.var .local (ofString "h"),.const 1099511628211]))
      (.return (.op .xor [.var .local (ofString "h"),.shift .lsr (.var .local (ofString "h")) (.const 29)])))

/-- The four checked word steps and final mix are the literal original32-byte
hash fast path, including its return. -/
theorem source_hash_fast32 : hashFast32 =
    hashWordThen 0 (hashWordThen 8 (hashWordThen 16 (hashWordThen 24 hashFinish))) := by rfl

#print axioms source_hash_fast32
end InitECandidate.Runtime

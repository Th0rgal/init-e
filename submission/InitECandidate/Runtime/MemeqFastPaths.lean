import InitECandidate.Runtime.MemeqChecks
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memeqAddress (name : MlS) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .var .local name else .op .add [.var .local name,.const (BitVec.ofNat 64 offset)]

def memeqWordPair (offset : Nat) : ExpHOL 64 × ExpHOL 64 :=
  (.load .one (memeqAddress (ofString "a") offset),.load .one (memeqAddress (ofString "b") offset))

def memeqBytePair (offset : Nat) : ExpHOL 64 × ExpHOL 64 :=
  (.loadByte (memeqAddress (ofString "a") offset),.loadByte (memeqAddress (ofString "b") offset))

def memeq20Checks := [memeqWordPair 0,memeqWordPair 8,memeqBytePair 16,memeqBytePair 17,memeqBytePair 18,memeqBytePair 19]
def memeq32Checks := [memeqWordPair 0,memeqWordPair 8,memeqWordPair 16,memeqWordPair 24]
def memeq52Checks := [memeqWordPair 0,memeqWordPair 8,memeqWordPair 16,memeqWordPair 24,memeqWordPair 32,
  memeqWordPair 40,memeqBytePair 48,memeqBytePair 49,memeqBytePair 50,memeqBytePair 51]

def memeqDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_memeq with | .function fn => fn.body | _ => .skip

def memeqAlignedBody : ProgHOL 64 :=
  match memeqDecodedBody with | .dec _ _ _ (.seq (.ite _ body _) _) => body | _ => .skip

def memeqFast20 : ProgHOL 64 :=
  match memeqAlignedBody with | .seq (.ite _ body _) _ => body | _ => .skip

def memeqFast32 : ProgHOL 64 :=
  match memeqAlignedBody with | .seq _ (.seq (.ite _ body _) _) => body | _ => .skip

def memeqFast52 : ProgHOL 64 :=
  match memeqAlignedBody with | .seq _ (.seq _ (.seq (.ite _ body _) _)) => body | _ => .skip

theorem source_memeq_fast20 : memeqFast20 = memeqChecks memeq20Checks := by rfl
theorem source_memeq_fast32 : memeqFast32 = memeqChecks memeq32Checks := by rfl
theorem source_memeq_fast52 : memeqFast52 = memeqChecks memeq52Checks := by rfl

#print axioms source_memeq_fast20
#print axioms source_memeq_fast32
#print axioms source_memeq_fast52
end InitECandidate.Runtime

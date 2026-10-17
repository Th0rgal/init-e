import InitECandidate.Runtime.StateRestoreLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Key width, initial capacity and transaction-state pointer offset, in the
exact order of the original constructors after the first local declaration. -/
def stateFreshTxRemainingTables : List (Nat × Nat × Nat) :=
  [(20,64,16),(52,64,24),(20,16,32),(52,16,40),(32,16,48),(20,16,56),(52,16,64)]

def stateFreshTxPointerStore (offset : Nat) : ProgHOL 64 :=
  .store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))

def stateFreshTxConstructorSequence : List (Nat × Nat × Nat) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | (width,capacity,offset) :: rest, tail =>
    .seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
      [.const (BitVec.ofNat 64 width),.const (BitVec.ofNat 64 capacity)])
      (.seq (stateFreshTxPointerStore offset) (stateFreshTxConstructorSequence rest tail))

theorem source_stateFreshTx_body : sourceFunctionBody Guest.guestFn_state_fresh_tx =
    .seq (.call (some (some (.global,ofString "ts"),none)) (ofString "alloc") [.const 72])
      (.seq (.store (.op .add [.var .global (ofString "ts"),.const 0]) (.var .global (ofString "bs")))
        (.decCall (ofString "t") .one (ofString "htab_new") [.const 20,.const 64]
          (.seq (stateFreshTxPointerStore 8)
            (stateFreshTxConstructorSequence stateFreshTxRemainingTables
              (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))))))) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

#print axioms source_stateFreshTx_body
end InitECandidate.Runtime

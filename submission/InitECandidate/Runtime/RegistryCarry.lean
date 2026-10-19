import InitECandidate.Runtime.BlockLayoutBridge
/-!
Recurrent registry lifetime across transactions. `regT_tab_facts_all`: in a registry with two distinct tables every
table's arrays lie below the heap pointer (its canonical-footprint separation from another table excludes the region
from the heap pointer on), so the block table's layout facts are available from any nine-table registry.
`stateFreshTx_regT9_carry`: the nine-table registry at the call of the original `state_fresh_tx` is re-established for
the new transaction's tables with the same block pre-state read table.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- In a registry with two distinct tables every table's arrays lie below the heap pointer: separation from the other
table excludes them from its canonical footprint, which contains everything from the heap pointer on. -/
theorem regT_tab_facts_all {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} (h : RegT n c T Out H M D B ko) (i j : Fin n) (ne : i ≠ j) :
    ∃ l : TLay, l.ok (T j) H ∧ l.hdr M (T j) ∧ M (c j) = .word (T j) ∧ ¬ l.canon (T j) H (c j) ∧
      ∀ x, l.arr x → x.toNat < H.toNat := by
  obtain ⟨l,pure,mem,_,_⟩ := h
  refine ⟨l j,(pure.1 j).1,(mem j).2,(mem j).1,(pure.1 j).2,fun x hx => ?_⟩
  by_contra hc
  exact pure.2.1 i j ne x (Or.inr (Or.inr hx)) (Or.inr (Or.inr (by omega)))

#print axioms regT_tab_facts_all

set_option maxHeartbeats 16000000 in
/-- Recurrent registry lifetime across transactions: if the nine-table registry holds when the original
`state_fresh_tx` is called (heap pointer, memory, domain and endianness of the calling state), the call re-establishes
it for the new transaction's tables with the same block pre-state read table. -/
theorem stateFreshTx_regT9_carry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldTs bs journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (journalBefore : journal.toNat + 524288 * 32 ≤ pointer.toNat)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ticks : 380 ≤ state.clock)
    (journalAligned : journal.toNat % 8 = 0)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (ts' p' bsC TB : BitVec 64) (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop) (B : Bool) (ko : Fin 9)
    (old : RegT 9 (c9 ts' p' bsC) (T9 p' TB) Out pointer state.memory D B ko) :
    ∃ (lB : TLay) (widths : BitVec 64 → BitVec 64) (post : PanSemStateFiniteExact 64 F) (H : BitVec 64),
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd pointer 72) pointer journal snapshot 0 post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ pointer.toNat ≤ H.toNat ∧
      (∀ ko : Fin 8, RegT 9 (c9 pointer (allocationEnd pointer 72) bsC) (T9 (allocationEnd pointer 72) TB)
        (fun x => x.toNat < pointer.toNat ∧ ¬ lB.canon TB pointer x) H post.memory post.memaddrs post.be
        ko.castSucc) := by
  obtain ⟨lB,ok,hdr,cell,off,arr⟩ := regT_tab_facts_all old 0 (Fin.last 8) (by decide)
  rw [T9_last] at ok hdr cell off; rw [c9_last] at cell off
  obtain ⟨widths,post,H,run,world,hH,pH,reg,_⟩ := stateFreshTx_regT9L state base pointer oldTs bs journal snapshot
    oldCount code heap tsGlobal bsGlobal journalGlobal counterGlobal reservation journalBefore domain ticks journalAligned
    capacityGlobal bsC TB lB ok hdr cell off arr
  exact ⟨lB,widths,post,H,run,world,hH,pH,reg⟩

#print axioms stateFreshTx_regT9_carry
end InitECandidate.Runtime

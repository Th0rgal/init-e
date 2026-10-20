import InitECandidate.Runtime.PtItemGD
import InitECandidate.Runtime.HtabTxOuter
/-!
Source-table validity for `incorporate_tx_into_block` (`SrcOK`, explicit at the reachable suffix state): the
transaction tables at `ts + 16` (accounts written) and `ts + 32` (storage outer map) have content (`TCont`), key length
at least 20 and count below capacity; every value named by a live order position of the outer map is an inner table
with content and key length at least 20. Bridge `srcOK_of_world` from root's `TransactionRegistryWorld` (ready
registered tables) with the outer map's values in a registered target set.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A table with content, key length at least 20 and count below capacity. -/
def SrcTabOK (D : BitVec 64 → Prop) (B : Bool) (M : Mem) (t : BitVec 64) (l : TLay) : Prop :=
  TCont D B M t l ∧ 20 ≤ l.KL.toNat ∧ l.N.toNat < l.C.toNat

/-- Source validity of the transaction tables read by `incorporate_tx_into_block`. -/
def SrcOK (D : BitVec 64 → Prop) (B : Bool) (M : Mem) (Ts : BitVec 64) : Prop :=
  ∃ (Taw Tout : BitVec 64) (law lout : TLay),
    (D (Ts + 16#64) ∧ M (Ts + 16#64) = .word Taw ∧ SrcTabOK D B M Taw law) ∧
    (D (Ts + 32#64) ∧ M (Ts + 32#64) = .word Tout ∧ SrcTabOK D B M Tout lout) ∧
    ∀ I slot vv : BitVec 64, I.toNat < lout.N.toNat → M (lout.OS + I * 8) = .word slot →
      M (lout.VS + slot * 8) = .word vv → ∃ li : TLay, SrcTabOK D B M vv li

section br
variable {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
  {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}

theorem TransactionRegistryWorld.srcTabOK (world : TransactionRegistryWorld widths tables fieldPointer ts journal
    snapshot count s) (al : RegistryAligned tables) (t : BitVec 64) (mem : t ∈ tables) :
    ∃ l : TLay, SrcTabOK s.memaddrs s.be s.memory t l ∧ HashOrderLinked l.US l.OS l.OPS l.C l.N s ∧
      HashValueEntriesWord l.US l.VS l.C s ∧ l.KL = widths t := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,inv,oi,room,_,linked,vword⟩ :=
    world.table_ready al t mem
  have kl : 20 ≤ (widths t).toNat := by
    rcases world.journalWorld.supported t mem with h | h | h <;> rw [h] <;> decide
  exact ⟨⟨widths t,stride,capacity,items,keys,values,used,order,orderPos,bits⟩,
    ⟨⟨F,s,rfl,rfl,rfl,inv.code,inv,oi⟩,kl,room⟩,linked,vword,rfl⟩

/-- `SrcOK` from the registry world: the fields at `ts + 16` and `ts + 32` are registered tables, and the outer map's
values lie in a registered target set. -/
theorem srcOK_of_world (world : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count s)
    (al : RegistryAligned tables) (Taw Tout : BitVec 64)
    (baw : (16,Taw) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (bout : (32,Tout) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (targets : Set (BitVec 64)) (valuesIn : HashTableValuesIn Tout targets s) (sub : targets ⊆ tables) :
    SrcOK s.memaddrs s.be s.memory ts := by
  obtain ⟨daw,caw,maw,_⟩ := world.field_source al 16 Taw baw (by decide)
  obtain ⟨dout,cout,mout,_⟩ := world.field_source al 32 Tout bout (by decide)
  obtain ⟨law,okaw,_,_,_⟩ := world.srcTabOK al Taw maw
  obtain ⟨lout,okout,linked,vword,_⟩ := world.srcTabOK al Tout mout
  refine ⟨Taw,Tout,law,lout,⟨daw,caw,okaw⟩,⟨dout,cout,okout⟩,fun I slot vv hI cO cV => ?_⟩
  have inv' := (TCont.toState okout.1 s rfl rfl rfl world.journalWorld.code).1
  obtain ⟨slot',slt,occ,cO'⟩ := linked.order_occupied_slot inv'.agreement I hI
  rw [cO] at cO'
  simp only [HolWordLab.word.injEq] at cO'
  subst cO'
  obtain ⟨u,cU⟩ := vword slot slt occ
  rw [cV] at cU
  simp only [HolWordLab.word.injEq] at cU
  subst cU
  have uT : vv ∈ tables := sub (valuesIn lout.C lout.US lout.VS inv'.cell16 inv'.cell48 inv'.cell40 slot slt occ vv cV)
  obtain ⟨li,ok,_⟩ := world.srcTabOK al vv uT
  exact ⟨li,ok⟩

#print axioms srcOK_of_world
end br
end InitECandidate.Runtime

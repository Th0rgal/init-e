import InitECandidate.Runtime.HtabMergeBound
import InitECandidate.Runtime.OriginalMergeTxCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The storage-side entry data only reads code, addresses, endianness, memory and globals. -/
theorem MergeStoreEntry.transfer {B T : BitVec 64} {ps : List UnionPair} {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {c : MergeCtx} {R : Set (BitVec 64)} {Z : BitVec 64 → Nat × Nat} (e : MergeStoreEntry B T ps s c R Z)
    (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (globals : r.globals = s.globals) : MergeStoreEntry B T ps r c R Z :=
  have core' := e.core.transfer memory memaddrs be code globals
  ⟨e.m0.trans memory.symm,e.a0.trans memaddrs.symm,e.be0.trans be.symm,e.g0.trans globals.symm,e.st,e.bd,core',
    e.outer.between e.core core',by rw [memaddrs]; exact e.dO,by rw [memory]; exact e.cO,e.fO,
    by rw [memaddrs]; exact e.dBO,by rw [memory]; exact e.cBO,e.fBO,by rw [memaddrs]; exact e.dn,
    by rw [memory]; exact e.cn,e.fn,e.apartO,
    fun bc bk bu bv bo bp bn bb inv => e.apartB bc bk bu bv bo bp bn bb
      (inv.transfer memory.symm memaddrs.symm be.symm code.symm),e.apartR⟩

#print axioms MergeStoreEntry.transfer

set_option maxHeartbeats 4000000 in
/-- All-outcome bound for an original call `merge_tx_into_block()` (any destination): the looked-up body from
the callee entry state, plus the call tick. -/
theorem runBounded_merge_tx_into_block_call (B T : BitVec 64) (ps : List UnionPair)
    (offsets : ps.map UnionPair.o = [24,8,40,16,48]) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (c : MergeCtx) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hT : s.globals.lookup (ofString "ts") = some (.val (.word T)))
    (ready : ∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T c.P0) (apart : ps.Pairwise (UnionPair.Apart B T))
    (entry : MergeStoreEntry B T ps s c R Z)
    (budget : (ps.map UnionPair.cost).sum + c.n.toNat * (c.iterCostK + 1) + 1 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (ofString "merge_tx_into_block") [])
      ((ps.map UnionPair.cost).sum + (c.n.toNat * (c.iterCostK + 1) + 0) + 1) := by
  refine RunBounded.call (values := []) (by rw [evalListHOLFinite_eq_toExact]; rfl) (by omega) ?_
  intro body locals returnShape lookup
  rw [pan_no_args_lookup _ _ _ (by rw [entry.core.1]; exact originalRuntimeCode_mergeTxIntoBlock_lookup)] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  let E := callEntryStateHOLFinite s HolFiniteMapExact.empty
  have eM : E.memory = s.memory ∧ E.memaddrs = s.memaddrs ∧ E.be = s.be ∧ E.code = s.code ∧ E.globals = s.globals ∧
      E.clock = s.clock - 1 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨m,a,b,cd,g,k⟩ := eM
  exact runBounded_merge_tx_into_block B T ps offsets E c R Z (by rw [g]; exact hB) (by rw [g]; exact hT)
    (fun q mem => ⟨q.ready_keep B T (ready q mem).1 a b cd (fun w _ => by rw [m]),(ready q mem).2⟩) apart
    (entry.transfer m a b cd g) (by rw [k]; omega)

#print axioms runBounded_merge_tx_into_block_call
end InitECandidate.Runtime

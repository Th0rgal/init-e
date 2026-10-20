import InitECandidate.Runtime.PtMergeGD
import InitECandidate.Runtime.HashTableValuesInSetCallAllPlans
import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
import InitECandidate.Runtime.HashTablePhysicalFrame
import InitECandidate.Runtime.TxRegistryBridge
/-!
Block-object tables with a values invariant. `TabRV D B T l Hl S M`: memory `M` (over the fixed domain `D` and
endianness `B`) holds at `T` a table with layout `l`, ready in root's sense (`HashTableReady`, at a heap frontier at most
`Hl`) and with every live value in the set `S` (`HashTableValuesIn`). The invariant only depends on the table's
physical region (`InTabF`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A ready table with live values in `S`. -/
def TabRV (D : BitVec 64 → Prop) (B : Bool) (T : BitVec 64) (l : TLay) (Hl : BitVec 64) (S : Set (BitVec 64))
    (M : Mem) : Prop :=
  ∃ (F : Type) (s : PanSemStateFiniteExact 64 F) (pointer : BitVec 64), s.memory = M ∧ s.memaddrs = D ∧ s.be = B ∧
    s.code = originalRuntimeCode ∧ pointer.toNat ≤ Hl.toNat ∧ 1 < l.C.toNat ∧ T.toNat % 8 = 0 ∧
    HashTableReady l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N l.b pointer s ∧ HashTableValuesIn T S s

/-- The physical region of a table with layout `l`. -/
def TabPhys (T : BitVec 64) (l : TLay) (x : BitVec 64) : Prop := InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x

section rv
variable {D : BitVec 64 → Prop} {B : Bool} {T : BitVec 64} {l : TLay} {Hl : BitVec 64} {S : Set (BitVec 64)}

theorem tabRV_frame {M M' : Mem} (h : TabRV D B T l Hl S M) (keep : ∀ x, TabPhys T l x → M' x = M x) :
    TabRV D B T l Hl S M' := by
  obtain ⟨F,s,P,hm,hd,hb,hc,hP,hC,hT,rd,vi⟩ := h
  let s' : PanSemStateFiniteExact 64 F := {s with memory := M'}
  have fr : ∀ address : BitVec 64, tablePhysicalRegion T l.KS l.SD l.C l.US l.VS l.OS l.OPS address →
      s'.memory address = s.memory address := fun a ha => by
    show M' a = s.memory a
    rw [hm]; exact keep a ((phys_iff_intabf _ _ _ _ _ _ _ _ _).mp ha)
  exact ⟨F,s',P,rfl,hd,hb,hc,hP,hC,hT,rd.physical_frame s s' _ _ _ _ _ _ _ _ _ _ _ _ fr rfl rfl rfl rfl,
    vi.physical_frame s s' _ _ _ _ _ _ _ _ _ _ _ rd.live.arrays S fr rfl rfl⟩

theorem tabRV_mono {M : Mem} {Hl' : BitVec 64} {S' : Set (BitVec 64)} (h : TabRV D B T l Hl S M)
    (le : Hl.toNat ≤ Hl'.toNat) (sub : S ⊆ S') : TabRV D B T l Hl' S' M := by
  obtain ⟨F,s,P,hm,hd,hb,hc,hP,hC,hT,rd,vi⟩ := h
  exact ⟨F,s,P,hm,hd,hb,hc,by omega,hC,hT,rd,vi.mono sub⟩

#print axioms tabRV_frame
#print axioms tabRV_mono
end rv
section an
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Strengthen the normal postcondition with any fact proven about the normally completing runs. -/
theorem aqgd_addNormal {P Q X : GA → Mem → GA → Prop} {p : ProgHOL 64} (h : AQGD D B A w Vn P Q RR p)
    (hn : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomD D B s → A s.globals →
      SL Vn s.locals → P s.locals s.memory s.globals → ∀ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s p = (none,post) → X post.locals post.memory post.globals) :
    AQGD D B A w Vn P (fun L M G => Q L M G ∧ X L M G) RR p := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl _ rfl pre
  refine ⟨m,a,fun e => ?_,r,c,b⟩
  obtain ⟨sl',H',hH',q⟩ := n e
  unfold GIs at hH'; subst hH'
  exact ⟨sl',_,rfl,q,hn s code dom aw sl pre _ (Prod.ext e rfl)⟩

#print axioms aqgd_addNormal
end an
end InitECandidate.Runtime

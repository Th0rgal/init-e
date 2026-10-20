import InitECandidate.Runtime.PtRestGD
/-!
Block-list utilities of the `process_transaction` suffix: both block lists (`BL2`), kept by registry writers (frames
of the outside words outside the journal and the key buffer, growing heap pointer) and by global updates other than
the heap pointer.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both block lists over the fresh words `[Hb, Hg)`. -/
def BL2 (W40 W72 : BitVec 64 → Prop) (Hb L40 L72 : BitVec 64) (M : Mem) (G : GA) : Prop :=
  BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G

section bu
variable {Out : BitVec 64 → Prop} {J C SKB : BitVec 64}

theorem bl_frameX {Wb : BitVec 64 → Prop} {Hb Lh Lo Hg H H' : BitVec 64} {M M' : Mem} {G G' : GA}
    (h : BL Wb Hb Lh 8#64 M G) (hW : ∀ x, Wb x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hH : HeapIs G H) (hH' : HeapIs G' H') (le : H.toNat ≤ H'.toNat)
    (keep : ∀ x, OutX Out Lo Hg x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M x) : BL Wb Hb Lh 8#64 M' G' :=
  bl_frame h (fun x hx => let k := hW x (h.1 x hx); keep x (Or.inl k.1) k.2.1 k.2.2)
    (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩)

theorem bl_gupd {Wb : BitVec 64 → Prop} {Hb Lh : BitVec 64} {M : Mem} {G : GA} (h : BL Wb Hb Lh 8#64 M G)
    (gname : MlS) (v : ValueHOL 64) (hn : ofString "heap_ptr" ≠ gname) : BL Wb Hb Lh 8#64 M (G.update (gname,v)) :=
  bl_frame h (fun _ _ => rfl) (fun H hH => ⟨H,by unfold HeapIs at *; rw [lookup_update_ne' _ _ hn]; exact hH,le_refl _⟩)

#print axioms bl_frameX
#print axioms bl_gupd
end bu
end InitECandidate.Runtime

import InitECandidate.Runtime.ArenaHoareMem
import InitECandidate.Runtime.ArenaBoundary
import InitECandidate.Runtime.HtabFindSlotReturned
import InitECandidate.Runtime.HashFindHashScope32
import InitECandidate.Runtime.OriginalHashCode
import InitECandidate.Runtime.HtabHashBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normalize a source function body and decide a Boolean syntactic check on it. -/
macro "body_check" fn:ident : tactic => `(tactic| (
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [$fn:ident,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  decide))

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- A read-only body (memory and globals kept in every outcome, no loop control) meets any spec whose returned
postcondition follows from a returned run, with the unchanged memory. -/
theorem aqm_of_mf {Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {RRe : ValueHOL 64 → Mem → Prop}
    {body : ProgHOL 64} (hmf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      AW SP0 P0 FM G0 s.globals → Pe s.locals s.memory →
      ∀ v post, evaluateHOLFiniteState s body = (some (.returned v),post) → RRe v s.memory) :
    AQM SP0 P0 FM G0 w (fun _ => False) Pe (fun _ _ => True) RRe body := by
  intro F s code dom aw sl pre
  obtain ⟨m,g⟩ := hmf s code
  refine ⟨by rw [m],fun _ => by rw [g]; exact aw,fun _ => ⟨fun _ h => h.elim,trivial⟩,fun v e => ?_,
    evaluate_noTopContinue body nc s,evaluate_noTopBreak body nb s⟩
  · rw [m]
    exact hret s code aw pre v _ (Prod.ext e rfl)

/-- A returned run of a scope that starts by loading `base + offset` read an addressable word. -/
theorem dec_load_returned_domain {F : Type} (s post : PanSemStateFiniteExact 64 F) (name base : MlS)
    (pointer offset : BitVec 64) (cont : ProgHOL 64) (v : ValueHOL 64)
    (binding : s.locals.lookup base = some (.val (.word pointer)))
    (run : evaluateHOLFiniteState s (.dec name .one (.load .one (hashLocalAddress base offset)) cont) =
      (some (.returned v),post)) : s.memaddrs (pointer + offset) := by
  by_contra hn
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  have ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (hashLocalAddress base offset)) = none := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress s base pointer offset binding]
    simp [memLoadHOLExact,hn]
  rw [ev] at run
  cases (Prod.mk.inj run).1

/-- `htab_find_slot` spec: memory unchanged, and a returned slot index is a word at most the capacity. -/
theorem findSlot_aqm (T C : BitVec 64) (b : Nat) (power : C.toNat = 2 ^ b) (M0 : Mem) :
    AQM SP0 P0 FM G0 w (fun _ => False)
      (fun L M => L.lookup (ofString "t") = some (.val (.word T)) ∧ M = M0 ∧ M (T + 16) = .word C)
      (fun _ _ => True) (fun v M' => M' = M0 ∧ ∃ i : BitVec 64, v = .val (.word i) ∧ i.toNat ≤ C.toNat)
      (sourceFunctionBody Guest.guestFn_htab_find_slot) := by
  refine aqm_of_mf htabFindSlot_memoryFrame (by rw [source_htabFind_header_prefix]; decide)
    (by rw [source_htabFind_header_prefix]; decide) ?_
  intro F s code _ ⟨ht,hm,hc⟩ v post run
  have run' := run
  rw [source_htabFind_header_prefix] at run'
  have d16 := dec_load_returned_domain s post _ _ T 16 _ v ht run'
  exact ⟨hm,htabFindSlot_returned_range s post T C b power ht d16 (hm ▸ hc) v run⟩

/-- `htab_hash` spec: memory unchanged. -/
theorem hash_aqm (M0 : Mem) :
    AQM SP0 P0 FM G0 w (fun _ => False) (fun _ M => M = M0) (fun _ _ => True) (fun _ M' => M' = M0)
      (sourceFunctionBody Guest.guestFn_htab_hash) :=
  aqm_of_mf (memoryFrame_leaf _ htabHash_readOnly) (by body_check Guest.guestFn_htab_hash)
    (by body_check Guest.guestFn_htab_hash)
    (fun _ _ _ hm _ _ _ => hm)

/-- A body that keeps its globals and changes memory only inside `Win` meets any spec whose returned
postcondition follows from that window. -/
theorem aqm_of_window {Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {RRe : ValueHOL 64 → Mem → Prop}
    {body : ProgHOL 64} (hg : OriginalGlobalsFrame body) (nb : noTopBreak body = true)
    (nc : noTopContinue body = true) (Win : BitVec 64 → Prop)
    (hwin : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → Pe s.locals s.memory →
      ∀ x, ¬ Win x → (evaluateHOLFiniteState s body).2.memory x = s.memory x)
    (hw : ¬ Win w)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → Pe s.locals s.memory →
      ∀ M' : Mem, (∀ x, ¬ Win x → M' x = s.memory x) → ∀ v, RRe v M') :
    AQM SP0 P0 FM G0 w (fun _ => False) Pe (fun _ _ => True) RRe body := by
  intro F s code dom aw sl pre
  refine ⟨hwin s code pre w hw,fun _ => by rw [hg s code]; exact aw,fun _ => ⟨fun _ h => h.elim,trivial⟩,
    fun v _ => hret s code pre _ (hwin s code pre) v,evaluate_noTopContinue body nc s,evaluate_noTopBreak body nb s⟩

/-- `memcpy(D, S, N)` spec: memory changes only inside the byte window of `[D, D + N)`. -/
theorem memcpy_aqm (D S N : BitVec 64) (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin D N.toNat w) (M0 : Mem) :
    AQM SP0 P0 FM G0 w (fun _ => False)
      (fun L M => L.lookup (ofString "dst") = some (.val (.word D)) ∧ L.lookup (ofString "src") = some (.val (.word S)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ M = M0)
      (fun _ _ => True) (fun _ M' => ∀ x, ¬ MWin D N.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memcpy) :=
  aqm_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
    (by body_check Guest.guestFn_memcpy) (MWin D N.toNat)
    (fun s _ ⟨hd,hs,hn,_⟩ x hx => memcpy_body_window s D S N x hd hs hn small hx) out
    (fun s _ ⟨_,_,_,hm⟩ M' hM' _ x hx => (hM' x hx).trans (congrFun hm x))

/-- `memzero(D, N)` spec: memory changes only inside the byte window of `[D, D + N)`. -/
theorem memzero_aqm (D N : BitVec 64) (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin D N.toNat w) (M0 : Mem) :
    AQM SP0 P0 FM G0 w (fun _ => False)
      (fun L M => L.lookup (ofString "dst") = some (.val (.word D)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        M = M0)
      (fun _ _ => True) (fun _ M' => ∀ x, ¬ MWin D N.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memzero) :=
  aqm_of_window memzero_body_globals_frame (by body_check Guest.guestFn_memzero)
    (by body_check Guest.guestFn_memzero) (MWin D N.toNat)
    (fun s _ ⟨hd,hn,_⟩ x hx => memzero_body_window s D N x hd hn small hx) out
    (fun s _ ⟨_,_,hm⟩ M' hM' _ x hx => (hM' x hx).trans (congrFun hm x))

/-- `alloc(N)` spec: memory unchanged; a returned block is the old heap pointer, 8-aligned, at or above `P0`, with
room for `N` bytes below `HEAP_END`. -/
theorem alloc_aqm (Nn : BitVec 64) (M0 : Mem) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0) (fun _ _ => True)
      (fun v M' => M' = M0 ∧ ∃ hp : BitVec 64, v = .val (.word hp) ∧ P0.toNat ≤ hp.toNat ∧
        hp.toNat + Nn.toNat ≤ 33806089496 ∧ hp.toNat % 8 = 0)
      (sourceFunctionBody Guest.guestFn_alloc) := by
  intro F s code dom aw sl ⟨hn,hm⟩
  obtain ⟨m,a,n,c,b⟩ := alloc_aq (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) F s code dom aw sl trivial
  have mk := alloc_memKeep s code
  refine ⟨m,a,fun e => ⟨(n e).1,trivial⟩,fun v e => ⟨by rw [mk,hm],?_⟩,c,b⟩
  obtain ⟨_,_,⟨hp,hhp,lo,hi,al⟩,_⟩ := aw
  obtain ⟨req,_,ew,_⟩ := alloc_body_returned s _ hp Nn code hhp hn v (Prod.ext e rfl)
  exact ⟨hp,ew,lo,allocationGuard_sum_bound hp Nn hi req,al⟩

#print axioms findSlot_aqm
#print axioms hash_aqm
#print axioms memcpy_aqm
#print axioms memzero_aqm
#print axioms alloc_aqm
end InitECandidate.Runtime

import InitECandidate.Runtime.ArenaHeapG
import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.AddSat
import InitECandidate.Runtime.VmFn_add_sat
import InitECandidate.Runtime.OriginalDispatchCode
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.OriginalBn254InitCode
import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.PreStateAccountHeap
/-!
The account branch of the original `prepare_dispatch()` (message word `msg + 24` zero) under the globals-aware triple
`AQMG (AWE .. E)` (arena globals plus `ev = E`): `get_pre_state_account` (heap-aware, lifted with the whole-program
`ev` frame), `acct_is_empty` (read-only) and `charge_state_gas` (writes only the three gas cells of `ev`) keep the
two-table invariant `PreTabs` from entry to every return.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- Arena globals plus a fixed frame-environment pointer `ev = E`. -/
def AWE (SP0 P0 FM : BitVec 64) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) (E : BitVec 64)
    (g : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  AW SP0 P0 FM G0 g ∧ g.lookup (ofString "ev") = some (.val (.word E))

/-- Words of the frame-environment record written by `charge_state_gas`. -/
def GasCells (E x : BitVec 64) : Prop := x = E + 64#64 ∨ x = E + 72#64 ∨ x = E + 192#64

theorem addSat_mf : MemoryFrame (sourceFunctionBody Guest.guestFn_add_sat) :=
  memoryFrame_leaf _ (by simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)


theorem ev_gas_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (E k : BitVec 64)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word E))) :
    EV s (.op .add [.var .global (ofString "ev"),.const k]) = some (.val (.word (E + k))) := by
  simp [EV,evalHOLExact,evalListHOLExact,hev,wordOpHOL,wordOp,valueIsWord,valueWord]

/-- A store into a gas cell of `ev` keeps every non-gas word and the heap pointer. -/
theorem gas_store {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} (E k : BitVec 64) (M0 : Mem)
    (H0 : BitVec 64) (hk : GasCells E (E + k)) (hw : ¬ GasCells E w) (v : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQMG (AWE SP0 P0 FM G0 E) w Vn (fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0)
      (fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) RR
      (.store (.op .add [.var .global (ofString "ev"),.const k]) v) := by
  refine aqmg_store _ _ (fun s H ⟨_,hev⟩ ⟨fr,hh⟩ _ => ⟨E + k,ev_gas_addr s E k hev,fun e => hw (e ▸ hk),
    fun y _ => ⟨fun x hx => ?_,hh⟩⟩) (fun s x _ _ _ _ ev => hv s x ev)
  have : x ≠ E + k := fun e => hx (e ▸ hk)
  simp only [if_neg this]
  exact fr x hx

set_option maxHeartbeats 4000000 in
/-- `charge_state_gas(amount)` with `ev = E`: the watched word (not a gas cell) is kept in every outcome (including
the out-of-gas exception); a return keeps the heap pointer and every word outside the three gas cells. -/
theorem chargeStateGas_aqmg (E : BitVec 64) (M0 : Mem) (H0 : BitVec 64) (hw : ¬ GasCells E w) :
    AQMG (AWE SP0 P0 FM G0 E) w (fun _ => True)
      (fun L M H => (∃ am : BitVec 64, L.lookup (ofString "amount") = some (.val (.word am))) ∧ M = M0 ∧ H = H0)
      (fun _ _ _ => True)
      (fun _ M' H' => H' = H0 ∧ ∀ x, ¬ GasCells E x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_charge_state_gas) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_charge_state_gas,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  have fr0 : ∀ M, M = M0 → ∀ x, ¬ GasCells E x → M x = M0 x := fun M e _ _ => by rw [e]
  refine aqmg_conseq (P := fun L M H => (∃ am : BitVec 64, L.lookup (ofString "amount") = some (.val (.word am))) ∧
      (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) ?_ (fun L M H ⟨h1,h2,h3⟩ => ⟨h1,fr0 M h2,h3⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- sgl, gl: loads of the gas words
  refine aqmg_dec (Pb := fun L M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) (Qb := fun _ _ _ => True) _ _ _
    (fun _ => rfl) (fun s v H _ ⟨_,fr,hh⟩ _ _ _ => ⟨fr,hh⟩) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqmg_dec (Pb := fun L M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) (Qb := fun _ _ _ => True) _ _ _
    (fun _ => rfl) (fun s v H _ h _ _ _ => h) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  -- enough state gas: one store, return
  refine aqmg_seq (Q := fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0)
    (aqmg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqmg_seq (aqmg_conseq (gas_store E 72#64 M0 H0 (Or.inr (Or.inl rfl)) hw _ (fun s x ev => ev_op_word s _ _ x ev))
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        (aqmg_return _ (fun _ _ _ _ h _ _ => ⟨h.2,h.1⟩)))
      (aqmg_conseq aqmg_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- tot = add_sat(sgl, gl): read-only
  refine aqmg_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0') (RRe := fun _ M0' H0' _ M' H' => M' = M0' ∧ H' = H0')
    (Pc := fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ vmLookup_add_sat (by simp)
    (fun _ M0' H0' _ => aqmg_of_mf addSat_mf (by body_check Guest.guestFn_add_sat)
      (by body_check Guest.guestFn_add_sat) M0' H0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L M H v M' H' h ⟨e1,e2⟩ _
    subst e1 e2; exact h
  -- spill into the regular gas: three stores, return; otherwise the out-of-gas exception
  refine aqmg_seq (Q := fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0)
    (aqmg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqmg_conseq aqmg_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqmg_seq (Q := fun _ _ _ => False) (aqmg_raise _ _) aqmg_false)
  refine aqmg_dec (Pb := fun _ M H => (∀ x, ¬ GasCells E x → M x = M0 x) ∧ H = H0) (Qb := fun _ _ _ => False) _ _ _
    (fun _ => rfl) (fun s v H _ h _ _ _ => h.1) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqmg_seq (gas_store E 72#64 M0 H0 (Or.inr (Or.inl rfl)) hw _
    (fun s x ev => by simp [EV,evalHOLExact] at ev; exact ⟨0,ev.symm⟩)) ?_
  refine aqmg_seq (gas_store E 64#64 M0 H0 (Or.inl rfl) hw _ (fun s x ev => ev_op_word s _ _ x ev)) ?_
  refine aqmg_seq (gas_store E 192#64 M0 H0 (Or.inr (Or.inr rfl)) hw _ (fun s x ev => ev_op_word s _ _ x ev)) ?_
  exact aqmg_return _ (fun _ _ _ _ h _ _ => ⟨h.2,h.1⟩)

#print axioms addSat_mf
#print axioms gas_store
#print axioms chargeStateGas_aqmg

theorem source_acctIsEmpty_body : sourceFunctionBody Guest.guestFn_acct_is_empty =
    (.seq (.ite (.cmp .notEqual (.load .one (.op .add [(.var .local (ofString "a")),(.const 0)])) (.const 0)) (.return (.const 0)) .skip) (.decCall (ofString "eq") .one (ofString "memeq") [(.load .one (.op .add [(.var .local (ofString "a")),(.const 48)])),(.var .global (ofString "empty_code_hash")),(.const 32)] (.seq (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0)) (.return (.const 0)) .skip) (.decCall (ofString "z") .one (ofString "u256_is_zero") [(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "a")),(.const 8)]))] (.return (.var .local (ofString "z"))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem acctIsEmpty_mf : MemoryFrame (sourceFunctionBody Guest.guestFn_acct_is_empty) := by
  have hz : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_is_zero) :=
    memoryFrame_leaf _ (by simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)
  have hm : MemoryFrame (sourceFunctionBody Guest.guestFn_memeq) := memoryFrame_leaf _ memeq_readOnlyMemory
  rw [source_acctIsEmpty_body]
  intro F state code
  exact memoryFrame_seq (memoryFrame_ite _ (memoryFrame_leaf _ (by decide)) (memoryFrame_leaf _ (by decide)))
    (memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup hm
      (memoryFrame_seq (memoryFrame_ite _ (memoryFrame_leaf _ (by decide)) (memoryFrame_leaf _ (by decide)))
        (memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_u256IsZero_lookup hz (memoryFrame_leaf _ (by decide)))))
    state code

/-- An installed body of an `ev`-good function passes the `ev`-keeping check. -/
theorem keepsEv_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : evGood f = true) :
    keepsG (ofString "ev") evGood body = true := by
  have := List.all_eq_true.mp ev_program_check _ (originalRuntimeCode_mem h)
  simpa [hf] using this

#print axioms acctIsEmpty_mf

theorem ev_load_goff {F : Type} (s : PanSemStateFiniteExact 64 F) (g : MlS) (X off : BitVec 64) (v : ValueHOL 64)
    (hx : s.globals.lookup g = some (.val (.word X)))
    (ev : EV s (.load .one (.op .add [.var .global g,.const off])) = some v) : v = .val (s.memory (X + off)) := by
  simp [EV,evalHOLExact,evalListHOLExact,hx,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact] at ev
  exact ev.2.symm

set_option maxHeartbeats 8000000 in
/-- Heap-aware `prepare_dispatch()` with `ev = E` on a message whose `msg + 24` word is zero (the account branch):
from `PreTabs` at entry, the watched word (outside both tables, below `P0`, outside the scratch/Keccak/nibble buffers
and the gas cells) is kept in every outcome, and every return re-establishes `PreTabs` at the exit heap pointer,
through `get_pre_state_account`, `acct_is_empty` and `charge_state_gas`. -/
theorem prepareDispatch_aqmg (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs))) (Ta Tb H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) (E Mg : BitVec 64) (hgw : ¬ GasCells E w)
    (hgas : ∀ x, (x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) → ¬ GasCells E x) :
    AQMG (AWE SP0 P0 FM G0 E) w (fun _ => True)
      (fun _ M H => H = H0 ∧ PreTabs Ts Bs Ta Tb (fun x => x = w) H0 M ∧ M (E + 112#64) = .word Mg ∧
        M (Mg + 24#64) = .word 0)
      (fun _ _ _ => True) (fun _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M')
      (sourceFunctionBody Guest.guestFn_prepare_dispatch) := by
  have keepPre : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      s.globals.lookup (ofString "ev") = some (.val (.word E)) →
      (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_get_pre_state_account)).2.globals.lookup
        (ofString "ev") = some (.val (.word E)) := fun s code hx =>
    (evaluate_keeps_ev _ (keepsEv_of_installed originalRuntimeCode_preStateAccountW_lookup (by decide_cbv)) s code).trans hx
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_prepare_dispatch,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  -- msg = lds (ev + 112)
  refine aqmg_dec (Pb := fun L M H => L.lookup (ofString "msg") = some (.val (.word Mg)) ∧ H = H0 ∧
      PreTabs Ts Bs Ta Tb (fun x => x = w) H0 M ∧ M (Mg + 24#64) = .word 0) (Qb := fun _ _ _ => False) _ _ _
    (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H ⟨_,hev⟩ ⟨hh,pt,hm,h24⟩ _ ev _
    rw [ev_load_goff s _ E 112#64 v hev ev,hm]
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],hh,pt,h24⟩
  -- the account branch is taken
  refine aqmg_seq (Q := fun _ _ _ => False) (aqmg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => False) _ ?_ ?_
    (aqmg_conseq aqmg_skip (fun _ _ _ h => h) (fun _ _ _ h => h.2.elim) (fun _ _ _ h => h))) aqmg_false
  · intro F s x H _ ⟨hmsg,_,_,h24⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    simp [EV,evalHOLExact,evalListHOLExact,hmsg,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,h24] at ev
    by_cases hd : s.memaddrs (Mg + 24#64)
    · simp [hd,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at ev
    · simp [hd] at ev
  -- pre = get_pre_state_account(lds (msg + 32))
  refine aqmg_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ _ H0' L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0' ∧
      PreTabs Ts Bs Ta Tb (fun x => x = w) H0' M)
    (RRe := fun _ _ _ _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M')
    (Pc := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_preStateAccountW_lookup (by simp)
    (fun _ _ H0' ⟨⟨_,he,_,_⟩,_⟩ => by
      subst he
      exact aqmg_strengthen (aqmh_iff_aqmg.mp (preStateAccountW_aqmh Ts Bs hTs hBs Ta Tb _ p0 K Pd NB hK0 hPd0 hNB0
        safe ws hp)) keepPre)
    ?_ (fun _ => rfl) (fun _ _ _ _ _ _ _ r _ => r) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H _ ⟨⟨hmsg,hh,pt,_⟩,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    cases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "msg"),.const 32#64])) with
    | none => simp [evalListHOLExact,hx] at args
    | some x =>
      obtain ⟨y,rfl⟩ := ev_load_one_word s _ x hx
      simp only [evalListHOLExact,hx,Option.map_some,Option.bind_some] at args
      simp at args
      subst args hh
      rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_preStateAccountW_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,pt⟩
  -- e = acct_is_empty(pre): read-only
  refine aqmg_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0') (RRe := fun _ M0' H0' _ M' H' => M' = M0' ∧ H' = H0')
    (Pc := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_acctIsEmpty_lookup (by simp)
    (fun _ M0' H0' _ => aqmg_of_mf acctIsEmpty_mf (by body_check Guest.guestFn_acct_is_empty)
      (by body_check Guest.guestFn_acct_is_empty) M0' H0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M H v M' H' pt ⟨e1,e2⟩ _
    subst e1 e2; exact pt
  -- if e != 0: charge_state_gas(183600); return 0
  refine aqmg_seq (Q := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M)
    (aqmg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqmg_conseq aqmg_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqmg_return _ (fun _ _ _ _ h _ _ => h))
  refine aqmg_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' H0' L M H => (∃ am : BitVec 64, L.lookup (ofString "amount") = some (.val (.word am))) ∧
      M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H' = H0' ∧ ∀ x, ¬ GasCells E x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_chargeStateGas_lookup (by simp)
    (fun _ M0' H0' _ => chargeStateGas_aqmg E M0' H0' hgw) ?_ ?_
  · intro F s values callee rs _ H _ _ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_chargeStateGas_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨183600,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M H v M' H' ⟨pt,_⟩ ⟨hh,fr⟩
    subst hh
    exact preTabs_frame pt (fun x hx => fr x (hgas x hx))

#print axioms prepareDispatch_aqmg
end InitECandidate.Runtime

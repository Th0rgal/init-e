import InitECandidate.Runtime.PtBalKeepGD
/-!
`bal_*` keeping across the `process_transaction` suffix after `process_message_call`: `goodBal2` = `goodGA`, the
`balExtra` closure, or one of the 18 further functions of the suffix call closure (`balSuf`, computed from the source
call graph: the functions reached from the statements after `out = process_message_call(m)` that are neither `goodGA`
nor in `balExtra`). `BalKeep2` (explicit premise, a whole-program decision like `BalKeep`) says each such body passes
`keepsG` for every `bal_*` global. Only `bal_init`, `execute_block` and `process_transaction` (and their callers) assign
the `bal_*` globals.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The further suffix functions (call closure of the suffix minus `goodGA` minus `balExtra`). -/
def balSuf : List MlS :=
  [ofString "acct_copy",
    ofString "acct_empty",
    ofString "acct_new",
    ofString "add_to_bloom",
    ofString "clear_account_preserving_balance",
    ofString "create_ether",
    ofString "destroy_account",
    ofString "destroy_storage",
    ofString "encode_receipt",
    ofString "frame_mem_release",
    ofString "get_account",
    ofString "get_account_optional",
    ofString "get_pre_state_account_optional",
    ofString "jdel",
    ofString "jset",
    ofString "logs_bloom",
    ofString "modify_state_commit",
    ofString "set_account"]

def balExtra2 : List MlS := balExtra ++ balSuf

def goodBal2 (f : MlS) : Bool := goodGA f || balExtra2.contains f

/-- Explicit premise: every `balExtra2` body keeps every `bal_*` global (relative to `goodBal2`). -/
def BalKeep2 : Prop :=
  ∀ w ∈ balWatched, ∀ f, balExtra2.contains f = true → ∀ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL), originalRuntimeCode.lookup f = some (params,body,rs) → keepsG w goodBal2 body = true



theorem keepsBal2_of_installed (bk : BalKeep2) {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {rs : ShapeHOL} (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodBal2 f = true) (w : MlS)
    (hw : w ∈ balWatched) : keepsG w goodBal2 body = true := by
  unfold goodBal2 at hf
  rcases Bool.or_eq_true_iff.mp hf with g | e
  · exact keepsG_of_keepsGA w goodGA goodBal2 (fun f h => by unfold goodBal2; rw [h]; rfl) body
      (keepsGA_of_installed h g)
  · exact bk w hw f e params body rs h

theorem goodBal2_bodies (bk : BalKeep2) (w : MlS) (hw : w ∈ balWatched) : ∀ f, goodBal2 f = true →
    ∀ values body callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs) →
    keepsG w goodBal2 body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  exact keepsBal2_of_installed bk hc hf w hw

section kb2
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A program passing `keepsG` for every `bal_*` global keeps `BalG`. -/
theorem aqgd_keepBal2 (bk : BalKeep2) {BA IA IS KB Ix : BitVec 64} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (hk : balWatched.all (fun g => keepsG g goodBal2 p) = true) (h : AQGD D B A w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ BalG BA IA IS KB Ix G) (fun L M G => Q L M G ∧ BalG BA IA IS KB Ix G)
      (fun v M G => RR v M G ∧ BalG BA IA IS KB Ix G) p := by
  intro F s code dom aw sl H hH ⟨pre,bg⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have keep : ∀ g ∈ balWatched, (evaluateHOLFiniteState s p).2.globals.lookup g = s.globals.lookup g := fun g hg =>
    evaluate_keepsG g goodBal2 (goodBal2_bodies bk g hg) p (List.all_eq_true.mp hk g hg) s code
  unfold GIs at hH; subst hH
  have bg' : BalG BA IA IS KB Ix (evaluateHOLFiniteState s p).2.globals := by
    obtain ⟨b1,b2,b3,b4,b5⟩ := bg
    exact ⟨(keep _ (by simp [balWatched])).trans b1,(keep _ (by simp [balWatched])).trans b2,
      (keep _ (by simp [balWatched])).trans b3,(keep _ (by simp [balWatched])).trans b4,
      (keep _ (by simp [balWatched])).trans b5⟩
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    unfold GIs at hH'; subst hH'
    exact ⟨sl',_,rfl,q,bg'⟩
  · obtain ⟨H',hH',q⟩ := r v e
    unfold GIs at hH'; subst hH'
    exact ⟨_,rfl,q,bg'⟩

#print axioms aqgd_keepBal2
end kb2
end InitECandidate.Runtime

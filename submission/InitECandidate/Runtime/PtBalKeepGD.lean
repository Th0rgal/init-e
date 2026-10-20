import InitECandidate.Runtime.PtNewRVGD
import InitECandidate.Runtime.GlobalKeepAllProgram
/-!
The block-access-list globals (`bal_accounts`, `bal_idx_accts`, `bal_idx_stor`, `bal_key_buf`, `bal_index`, assigned
only in `bal_init`) are not static, so their values across callees come from the syntactic global-keep checker
(`keepsG`). `goodBal` = root's `goodGA` (all globals kept, whole-program checked) or one of the 49 other functions of the
`incorporate_tx_into_block` call closure (`balExtra`, computed from the source call graph). `BalKeep` (explicit premise,
a whole-program decision like `program_check_bo`) says each `balExtra` body passes `keepsG` for every `bal_*` global.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def balExtra : List MlS :=
  [ofString "_decode_step",ofString "_decode_witness_node",ofString "_decode_witness_node_body",
    ofString "_decode_witness_node_mpt",ofString "_resolve_step",ofString "_rlp_validate_items_body",
    ofString "add_balance_change",ofString "add_code_change",ofString "add_nonce_change",
    ofString "add_storage_write",ofString "alloc",ofString "bal_ensure_account",ofString "compact_to_nibbles",
    ofString "decode_account_from_leaf",ofString "decode_witness_to_mpt",ofString "get_code",
    ofString "get_pre_tx_account",ofString "get_pre_tx_storage",ofString "heap_release",ofString "htab_grow",
    ofString "htab_new",ofString "htab_set",ofString "htab_union_into",ofString "idx_start_account",
    ofString "idx_start_storage",ofString "incorporate_tx_into_block",ofString "lst_new",ofString "lst_push",
    ofString "lst_upsert_idx",ofString "merge_tx_into_block",ofString "node_new_branch",
    ofString "node_new_ext",ofString "node_new_hashed",ofString "node_new_leaf",
    ofString "record_pre_state_read",ofString "rlp_decode_fully",ofString "rlp_item",
    ofString "rlp_item_total",ofString "rlp_list_count",ofString "rlp_list_to_slices",
    ofString "rlp_validate_items",ofString "scratch_alloc",ofString "scratch_release",
    ofString "update_builder_from_tx",ofString "ws_account_leaf",ofString "ws_get_account_optional",
    ofString "ws_get_storage",ofString "ws_storage_root_of",ofString "ws_storage_trie"]

def goodBal (f : MlS) : Bool := goodGA f || balExtra.contains f

def balWatched : List MlS :=
  [ofString "bal_accounts",ofString "bal_idx_accts",ofString "bal_idx_stor",ofString "bal_key_buf",ofString "bal_index"]

/-- Explicit premise: every `balExtra` body keeps every `bal_*` global (relative to `goodBal`). -/
def BalKeep : Prop :=
  ∀ w ∈ balWatched, ∀ f, balExtra.contains f = true → ∀ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL), originalRuntimeCode.lookup f = some (params,body,rs) → keepsG w goodBal body = true

theorem keepsG_of_keepsGA (w : MlS) (good good' : MlS → Bool) (hg : ∀ f, good f = true → good' f = true) :
    (p : ProgHOL 64) → keepsGA good p = true → keepsG w good' p = true
  | .dec _ _ _ body, h => keepsG_of_keepsGA w good good' hg body h
  | .seq a b, h => by
    simp only [keepsGA,keepsG,Bool.and_eq_true] at h ⊢
    exact ⟨keepsG_of_keepsGA w good good' hg a h.1,keepsG_of_keepsGA w good good' hg b h.2⟩
  | .ite _ a b, h => by
    simp only [keepsGA,keepsG,Bool.and_eq_true] at h ⊢
    exact ⟨keepsG_of_keepsGA w good good' hg a h.1,keepsG_of_keepsGA w good good' hg b h.2⟩
  | .while _ body, h => keepsG_of_keepsGA w good good' hg body h
  | .decCall _ _ f _ k, h => by
    simp only [keepsGA,keepsG,Bool.and_eq_true] at h ⊢
    exact ⟨hg f h.1,keepsG_of_keepsGA w good good' hg k h.2⟩
  | .call none f _, h => by simp only [keepsGA,keepsG] at h ⊢; exact hg f h
  | .call (some (none,none)) f _, h => by simp only [keepsGA,keepsG] at h ⊢; exact hg f h
  | .call (some (some (.local,_),none)) f _, h => by simp only [keepsGA,keepsG] at h ⊢; exact hg f h
  | .call (some (none,some (_,_,hp))) f _, h => by
    simp only [keepsGA,keepsG,Bool.and_eq_true] at h ⊢
    exact ⟨hg f h.1,keepsG_of_keepsGA w good good' hg hp h.2⟩
  | .call (some (some (.local,_),some (_,_,hp))) f _, h => by
    simp only [keepsGA,keepsG,Bool.and_eq_true] at h ⊢
    exact ⟨hg f h.1,keepsG_of_keepsGA w good good' hg hp h.2⟩
  | .call (some (some (.global,_),_)) f _, h => by simp [keepsGA] at h
  | .assign .local _ _, _ => rfl
  | .assign .global _ _, h => by simp [keepsGA] at h
  | .store _ _, _ => rfl
  | .storeByte _ _, _ => rfl
  | .skip, _ => rfl
  | .break, _ => rfl
  | .continue, _ => rfl
  | .annot _ _, _ => rfl
  | .raise _ _, _ => rfl
  | .return _, _ => rfl
  | .extCall _ _ _ _ _, _ => rfl
  | .primitive _ _ _, _ => rfl
  | .shMemStore _ _ _, _ => rfl
  | .store32 _ _, h => by simp [keepsGA] at h
  | .shMemLoad _ _ _ _, h => by simp [keepsGA] at h
  | .tick, h => by simp [keepsGA] at h
#print axioms keepsG_of_keepsGA

theorem keepsBal_of_installed (bk : BalKeep) {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {rs : ShapeHOL} (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodBal f = true) (w : MlS)
    (hw : w ∈ balWatched) : keepsG w goodBal body = true := by
  unfold goodBal at hf
  rcases Bool.or_eq_true_iff.mp hf with g | e
  · exact keepsG_of_keepsGA w goodGA goodBal (fun f h => by unfold goodBal; rw [h]; rfl) body
      (keepsGA_of_installed h g)
  · exact bk w hw f e params body rs h

theorem goodBal_bodies (bk : BalKeep) (w : MlS) (hw : w ∈ balWatched) : ∀ f, goodBal f = true →
    ∀ values body callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs) →
    keepsG w goodBal body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  exact keepsBal_of_installed bk hc hf w hw

/-- The `bal_*` globals at fixed values. -/
def BalG (BA IA IS KB Ix : BitVec 64) (G : GA) : Prop :=
  G.lookup (ofString "bal_accounts") = some (.val (.word BA)) ∧
  G.lookup (ofString "bal_idx_accts") = some (.val (.word IA)) ∧
  G.lookup (ofString "bal_idx_stor") = some (.val (.word IS)) ∧
  G.lookup (ofString "bal_key_buf") = some (.val (.word KB)) ∧
  G.lookup (ofString "bal_index") = some (.val (.word Ix))

section kb
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A program passing `keepsG` for every `bal_*` global keeps `BalG`. -/
theorem aqgd_keepBal (bk : BalKeep) {BA IA IS KB Ix : BitVec 64} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (hk : balWatched.all (fun g => keepsG g goodBal p) = true) (h : AQGD D B A w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ BalG BA IA IS KB Ix G) (fun L M G => Q L M G ∧ BalG BA IA IS KB Ix G)
      (fun v M G => RR v M G ∧ BalG BA IA IS KB Ix G) p := by
  intro F s code dom aw sl H hH ⟨pre,bg⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have keep : ∀ g ∈ balWatched, (evaluateHOLFiniteState s p).2.globals.lookup g = s.globals.lookup g := fun g hg =>
    evaluate_keepsG g goodBal (goodBal_bodies bk g hg) p (List.all_eq_true.mp hk g hg) s code
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

#print axioms aqgd_keepBal
end kb
end InitECandidate.Runtime

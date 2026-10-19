import InitECandidate.Runtime.HtabCopyFrame
import InitECandidate.Runtime.OriginalHashHasCode
import InitECandidate.Runtime.OriginalHashGetCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htabHasTail : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_htab_has with | .decCall _ _ _ _ tail => tail | _ => .skip

def htabGetTail : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_htab_get with | .decCall _ _ _ _ tail => tail | _ => .skip

theorem source_htabHas_full : sourceFunctionBody Guest.guestFn_htab_has = (.decCall (ofString "i") .one (ofString "htab_find_slot") [(.var .local (ofString "t")),(.var .local (ofString "key"))] (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.load .one (.op .add [(.var .local (ofString "t")),(.const 16)]))) (.return (.const 0)) .skip) (.return (.const 1)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_htabGet_full : sourceFunctionBody Guest.guestFn_htab_get = (.decCall (ofString "i") .one (ofString "htab_find_slot") [(.var .local (ofString "t")),(.var .local (ofString "key"))] (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.load .one (.op .add [(.var .local (ofString "t")),(.const 16)]))) (.return (.rstruct [(.const 0),(.const 0)])) .skip) (.return (.rstruct [(.const 1),(.load .one (.op .add [(.load .one (.op .add [(.var .local (ofString "t")),(.const 40)])),(.panop .mul [(.var .local (ofString "i")),(.const 8)])]))])))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_htabHas_body : sourceFunctionBody Guest.guestFn_htab_has =
    .decCall (ofString "i") .one (ofString "htab_find_slot") [.var .local (ofString "t"),.var .local (ofString "key")] htabHasTail := by
  unfold htabHasTail
  generalize hb : sourceFunctionBody Guest.guestFn_htab_has = b
  rw [source_htabHas_full] at hb
  subst hb
  rfl

theorem source_htabGet_body : sourceFunctionBody Guest.guestFn_htab_get =
    .decCall (ofString "i") .one (ofString "htab_find_slot") [.var .local (ofString "t"),.var .local (ofString "key")] htabGetTail := by
  unfold htabGetTail
  generalize hb : sourceFunctionBody Guest.guestFn_htab_get = b
  rw [source_htabGet_full] at hb
  subst hb
  rfl

theorem htabHasTail_straight : extStraightLine htabHasTail = true := by
  unfold htabHasTail; rw [source_htabHas_full]; decide
theorem htabGetTail_straight : extStraightLine htabGetTail = true := by
  unfold htabGetTail; rw [source_htabGet_full]; decide
theorem htabHasTail_readOnly : readOnlyMemory htabHasTail = true := by
  unfold htabHasTail; rw [source_htabHas_full]; decide
theorem htabGetTail_readOnly : readOnlyMemory htabGetTail = true := by
  unfold htabGetTail; rw [source_htabGet_full]; decide

#print axioms source_htabHas_body
#print axioms htabGetTail_straight

/-- The original `htab_has` body on an aligned table with a free slot spends at
most the lookup bound plus one tick in every outcome. -/
theorem evaluate_htabHas_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + 0 ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_has)
      (keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + 0) := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← inv.agreement]; exact room)
  rw [source_htabHas_body]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  exact runBounded_htabFindSlot_decCall state _ _ _ htabHasTail table key capacity keyLength stride keys used empty bits inv.code args
    (inv.header_domain 16 (by omega) (by omega)) inv.cell16 (inv.header_domain 0 (by omega) (by omega)) inv.cell0
    (inv.header_domain 8 (by omega) (by omega)) inv.cell8 (inv.header_domain 32 (by omega) (by omega)) inv.cell32
    (inv.header_domain 48 (by omega) (by omega)) inv.cell48 inv.power emptyInside
    (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small budget
    (fun value post c _ _ _ => RunBounded.ofProg (ProgBounded.straight _ htabHasTail_straight)
      (by change post.code = _; rw [c]; exact inv.code) (Nat.zero_le _))

/-- `htab_has` changes neither memory nor globals, in every outcome. -/
theorem htabHas_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_has) := by
  rw [source_htabHas_body]
  exact memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup htabFindSlot_memoryFrame
    (memoryFrame_leaf _ htabHasTail_readOnly)

theorem htabHas_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_has) := by
  apply normalRel_of_frame heapRel_preorder
  intro F state code
  exact (htabHas_memoryFrame state code).2

#print axioms evaluate_htabHas_body_bounded
#print axioms htabHas_memoryFrame
#print axioms htabHas_normalRel

/-- The original `htab_get` body on an aligned table with a free slot spends at
most the lookup bound plus one tick in every outcome. -/
theorem evaluate_htabGet_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + 0 ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_get)
      (keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 + 0) := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← inv.agreement]; exact room)
  rw [source_htabGet_body]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  exact runBounded_htabFindSlot_decCall state _ _ _ htabGetTail table key capacity keyLength stride keys used empty bits inv.code args
    (inv.header_domain 16 (by omega) (by omega)) inv.cell16 (inv.header_domain 0 (by omega) (by omega)) inv.cell0
    (inv.header_domain 8 (by omega) (by omega)) inv.cell8 (inv.header_domain 32 (by omega) (by omega)) inv.cell32
    (inv.header_domain 48 (by omega) (by omega)) inv.cell48 inv.power emptyInside
    (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small budget
    (fun value post c _ _ _ => RunBounded.ofProg (ProgBounded.straight _ htabGetTail_straight)
      (by change post.code = _; rw [c]; exact inv.code) (Nat.zero_le _))

/-- `htab_get` changes neither memory nor globals, in every outcome. -/
theorem htabGet_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_get) := by
  rw [source_htabGet_body]
  exact memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup htabFindSlot_memoryFrame
    (memoryFrame_leaf _ htabGetTail_readOnly)

theorem htabGet_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_get) := by
  apply normalRel_of_frame heapRel_preorder
  intro F state code
  exact (htabGet_memoryFrame state code).2

#print axioms evaluate_htabGet_body_bounded
#print axioms htabGet_memoryFrame
#print axioms htabGet_normalRel

theorem htabCount_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_count) := by
  apply memoryFrame_leaf
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  decide

theorem htabCap_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_cap) := by
  apply memoryFrame_leaf
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  decide

theorem htabSlot_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_slot) := by
  apply memoryFrame_leaf
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  decide

#print axioms htabCount_memoryFrame
#print axioms htabCap_memoryFrame
#print axioms htabSlot_memoryFrame
end InitECandidate.Runtime

import InitECandidate.Runtime.HashNewZero
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute occupancy clearing before any remaining constructor suffix. Only
the allocated occupancy interval needs to fit; later allocations may fail. -/
theorem evaluate_htabNew_zero_runtime_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table used capacity : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 1 ≤ state.clock)
    (small : used.toNat + capacity.toNat ≤ 33806089496)
    (aligned : used.toNat % 8 = 0)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (headerDomain : state.memaddrs (table + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (used + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (used + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state (htabNewZeroPrefix continuation) = evaluateHOLFiniteState ready continuation ∧
      state.clock ≤ ready.clock + capacity.toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word used),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,_⟩ :=
    evaluate_memzero_aligned_call state _ _ used capacity arguments code ticks
      small aligned wordDomain byteDomain
  have t : post.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [locals]; exact tableLocal
  have u : post.locals.lookup (ofString "used") = some (.val (.word used)) := by
    rw [locals]; exact usedLocal
  have store := evaluate_store_word post (table + 48) used
    _ (.var .local (ofString "used")) (eval_hashLocalAddress post (ofString "t") table 48 t) u
    (by rw [domain]; exact headerDomain)
  let ready := sourceWriteWord post (table + 48) used
  refine ⟨ready,?_,cost,remaining,locals,globals,postCode,domain,endian⟩
  · unfold htabNewZeroPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store]

#print axioms evaluate_htabNew_zero_runtime_prefix
end InitECandidate.Runtime

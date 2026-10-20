import InitECandidate.Runtime.StateInitWorldPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual world-record allocation and its three input stores, before witness
decoding. One allocator clock is spent; older memory and caller locals remain. -/
theorem evaluate_state_init_world_prefix_exact_room {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldWs nodes root codes : BitVec 64) (tail : ProgHOL 64)
    (code : s.code = originalRuntimeCode) (ticks : s.clock ≠ 0)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ws : s.globals.lookup (ofString "ws") = some (.val (.word oldWs)))
    (nodeLocal : s.locals.lookup (ofString "nodedb") = some (.val (.word nodes)))
    (rootLocal : s.locals.lookup (ofString "state_root") = some (.val (.word root)))
    (codeLocal : s.locals.lookup (ofString "codedb") = some (.val (.word codes)))
    (room : pointer.toNat + 40 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (stateInitWorldPrefix tail) = evaluateHOLFiniteState post tail ∧
      post.clock = s.clock - 1 ∧ post.locals = s.locals ∧ post.code = s.code ∧
      post.memaddrs = s.memaddrs ∧ post.be = s.be ∧
      post.globals.lookup (ofString "ws") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 40))) ∧
      post.memory (pointer + 0) = .word nodes ∧ post.memory (pointer + 8) = .word root ∧
      post.memory (pointer + 16) = .word codes ∧
      (∀ a : BitVec 64, a.toNat < pointer.toNat → post.memory a = s.memory a) ∧
      (∀ name, name ≠ ofString "ws" → name ≠ ofString "heap_ptr" →
        post.globals.lookup name = s.globals.lookup name) := by
  have request : (40#64) ≤ (33806089496#64) - pointer := by
    apply BitVec.le_def.mpr
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change pointer.toNat ≤ 33806089496; omega)]
    change 40 ≤ 33806089496 - pointer.toNat
    omega
  obtain ⟨allocated,run,clock,memory,locals,installed,addrs,endian,atWs,atHeap,globals⟩ :=
    evaluate_alloc_global_call s (.const 40) pointer 40 oldWs (ofString "ws")
      (by rw [evalListHOLFinite_eq_toExact]; rfl) code ticks heap ws (by decide) request
      (allocationEnd_within_heap pointer 40 (by omega) request)
  have off (n : Nat) (inside : n < 40) : (pointer + BitVec.ofNat 64 n).toNat = pointer.toNat + n :=
    off_toNat pointer n (by omega) (by omega)
  let a := sourceWriteWord allocated (pointer + 0) nodes
  let b := sourceWriteWord a (pointer + 8) root
  let post := sourceWriteWord b (pointer + 16) codes
  have store0 := evaluate_store_word allocated (pointer + 0) nodes
    (.op .add [.var .global (ofString "ws"),.const 0]) (.var .local (ofString "nodedb"))
    (by simp [evalHOLExact,evalListHOLExact,atWs,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,locals,nodeLocal]) (by rw [addrs]; exact domain _ (by change (pointer + BitVec.ofNat 64 0).toNat < 33806089496; rw [off 0 (by decide)]; omega))
  have store8 := evaluate_store_word a (pointer + 8) root
    (.op .add [.var .global (ofString "ws"),.const 8]) (.var .local (ofString "state_root"))
    (by simp [evalHOLExact,evalListHOLExact,a,sourceWriteWord,atWs,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,a,sourceWriteWord,locals,rootLocal])
    (by change allocated.memaddrs _; rw [addrs]; exact domain _ (by change (pointer + BitVec.ofNat 64 8).toNat < 33806089496; rw [off 8 (by decide)]; omega))
  have store16 := evaluate_store_word b (pointer + 16) codes
    (.op .add [.var .global (ofString "ws"),.const 16]) (.var .local (ofString "codedb"))
    (by simp [evalHOLExact,evalListHOLExact,b,a,sourceWriteWord,atWs,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,b,a,sourceWriteWord,locals,codeLocal])
    (by change allocated.memaddrs _; rw [addrs]; exact domain _ (by change (pointer + BitVec.ofNat 64 16).toNat < 33806089496; rw [off 16 (by decide)]; omega))
  refine ⟨post,?_,clock,locals,installed,addrs,endian,atWs,atHeap,?_,?_,?_,?_,globals⟩
  · unfold stateInitWorldPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store0]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store8]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store16]
  · simp [post,b,a,sourceWriteWord]
  · simp [post,b,a,sourceWriteWord]
  · simp [post,sourceWriteWord]
  · intro address below
    have ne (n : Nat) (inside : n < 40) : address ≠ pointer + BitVec.ofNat 64 n := by
      intro equal
      rw [equal,off n inside] at below
      omega
    have n0 : address ≠ pointer + 0 := ne 0 (by decide)
    have n8 : address ≠ pointer + 8 := ne 8 (by decide)
    have n16 : address ≠ pointer + 16 := ne 16 (by decide)
    simpa only [post,b,a,sourceWriteWord,if_neg n16,if_neg n8,if_neg n0] using congrFun memory address

#print axioms evaluate_state_init_world_prefix_exact_room
end InitECandidate.Runtime

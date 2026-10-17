import InitECandidate.Runtime.JournalAllocationFailure32
import InitECandidate.Runtime.JournalDeleteAbsent32
import InitECandidate.Runtime.JournalDeleteLookup32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_journalDelete_after_get_allocation_failure32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (present value count capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (room : count.toNat < capacity.toNat)
    (pointer table : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain : state.memaddrs (table + 0)) (cell : state.memory (table + 0) = .word (32 : BitVec 64))
    (failure : ((33806089496 : BitVec 64) - pointer).toNat < 32) :
    (evaluateHOLFiniteState state journalDeleteAfterGet32).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state journalDeleteAfterGet32).2.clock + 2 ∧
      (evaluateHOLFiniteState state journalDeleteAfterGet32).2.clock ≤ state.clock := by
  by_cases absent : present = 0
  · rw [evaluate_journalDelete_absent32 state value (by simpa [absent] using old)]
    exact ⟨by simp,by change state.clock ≤ state.clock + 2; omega,by rfl⟩
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      have notZero : present ≠ (0#64) := absent
      simp [evalHOLExact,old,Compiler.Encoders.Asm.wordCmpHOL,notZero]
    have selected : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    have run : evaluateHOLFiniteState state journalDeleteAfterGet32 = evaluateHOLFiniteState state journalDeletePresent32 :=
      evaluate_seq_none selected rfl
    have overflow := evaluate_journal_delete_allocation_failure32 state table pointer count capacity code heap t countGlobal capacityGlobal room domain cell failure
    rw [run]
    refine ⟨overflow.1,?_,?_⟩ <;> rw [overflow.2] <;> omega

/-- Full original jdel terminates on journal overflow after its bounded lookup,
without requiring allocator, copy, or growth assumptions. -/
theorem HashTableReady32.jdel_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key count journalCapacity : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)])
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (room : count.toNat < journalCapacity.toNat)
    (failure : ((33806089496 : BitVec 64) - pointer).toNat < 32) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock + 2 * capacity.toNat + 5 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock ≤ state.clock := by
  obtain ⟨present,value,looked,_,lookupReady,old,cost,remaining,_,globals,_,_,_,locals,run⟩ :=
    ready.jdel_lookup state table pointer keys stride capacity used values order orderPos items key bits arguments keyAligned keyDomain budget
  have overflow := evaluate_journalDelete_after_get_allocation_failure32 looked present value count journalCapacity lookupReady.live.arrays.code old
    (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal) room pointer table
    lookupReady.live.frontier.heap ((locals (ofString "t") (by decide)).trans t)
    (lookupReady.live.arrays.header_domain looked table keys stride capacity used values order orderPos items bits 0 (by decide))
    lookupReady.live.arrays.cell0 failure
  rw [run]
  dsimp only
  refine ⟨overflow.1,?_,?_⟩
  ·
    have bound := overflow.2.1
    have below := overflow.2.2
    omega
  ·
    have bound := overflow.2.1
    have below := overflow.2.2
    omega

#print axioms evaluate_journalDelete_after_get_allocation_failure32
#print axioms HashTableReady32.jdel_allocation_failure
end InitECandidate.Runtime

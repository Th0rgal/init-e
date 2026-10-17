import InitECandidate.Runtime.StateFreshTxWidthExtension
import InitECandidate.Runtime.StateFreshTxDeclarationSequenceReset
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual eight table constructors and reset establish the empty rollback
world with an existentially constructed width map, from an empty table registry. -/
theorem evaluate_stateFreshTx_tables_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer ts journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (aligned : pointer.toNat % 8 = 0)
    (headerBefore : ts.toNat + 72 ≤ pointer.toNat)
    (journalBefore : journal.toNat ≤ ts.toNat + 72)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : pointer.toNat + 22944 ≤ 33806089496) (ticks : 336 ≤ state.clock) :
    ∃ widths post, evaluateHOLFiniteState state
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 20,.const 64]
        (.seq (stateFreshTxPointerStore 8) (stateFreshTxConstructorSequence stateFreshTxRemainingTables
          (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0)))))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),
        {emptyLocalsHOLFinite post with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite post).locals (ofString "t",state.locals.lookup (ofString "t"))}) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter pointer stateFreshTxAllTables ∅) journal snapshot 0
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter pointer stateFreshTxAllTables ∅) post ∧
      state.clock ≤ post.clock + 336 ∧ post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧
      (∀ address, address.toNat < pointer.toNat → widths address = base address) := by
  obtain ⟨widths,plan,preserve⟩ := stateFreshTx_all_width_extension base pointer budget
  have firstWidth : widths pointer = (20 : BitVec 64) := plan.1
  have restPlan : StateFreshTxPlan widths (stateFreshTxNextTable pointer 20 64) stateFreshTxRemainingTables := plan.2.2.2.2.2.2
  have firstNat : (widths pointer).toNat = 20 := by rw [firstWidth]; rfl
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 20,.const 64] =
      some [.val (.word (widths pointer)),.val (.word (64 : BitVec 64))] := by
    rw [firstWidth]; rfl
  obtain ⟨post,run,world,apart,cost,remaining,addresses⟩ :=
    evaluate_stateFreshTx_declaration_sequence_reset state widths ∅ (.const 20) (.const 64) pointer 64 6 arguments (by decide) code stateFreshTxRemainingTables
      (by simpa [stateFreshTx_remaining_budgets.2] using ticks) heap (by omega) aligned
      (by simpa [stateFreshTx_remaining_budgets.1] using budget) (by decide)
      (by intro other member; exact False.elim member)
      (by intro left leftMember; exact False.elim leftMember)
      ts 8 tsGlobal (by decide) domain headerBefore
      (by intro other member; exact False.elim member)
      (by simpa [stateFreshTxNextTable,firstWidth] using restPlan)
      journal snapshot oldCount journalGlobal counterGlobal journalBefore
  refine ⟨widths,post,?_,?_,?_,?_,remaining,addresses,preserve⟩
  · exact run
  · simpa [stateFreshTxAllTables,stateFreshTxRegistryAfter,stateFreshTxNextTable,firstWidth] using world
  · simpa [stateFreshTxAllTables,stateFreshTxRegistryAfter,stateFreshTxNextTable,firstWidth] using apart
  · simpa [stateFreshTx_remaining_budgets.2,Nat.add_assoc] using cost

#print axioms evaluate_stateFreshTx_tables_ready
end InitECandidate.Runtime

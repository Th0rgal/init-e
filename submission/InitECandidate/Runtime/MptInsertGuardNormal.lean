import InitECandidate.Runtime.MptInsertKindDispatchBound
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Normal completion of the actual invalid-kind guard proves the loaded kind
is nonzero. The real mpt_fail call cannot fall through at any clock. -/
theorem mpt_insert_guard_normal_identity {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (kind : BitVec 64) (atKind : s.locals.lookup (ofString "k")=some (.val (.word kind)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertKindGuard=(none,post)) : kind≠0#64 ∧post=s := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "k")) (.const 0))=some (.val (.word (if kind=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atKind,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_mptInsert_kind_guard,evaluateHOLFiniteState_ite,cmp] at run
 by_cases zero : kind=0#64
 · have zeroRaw : kind=0:=zero
   simp only [if_pos zero,show (1#64)≠0 from by decide,if_false] at run
   change evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const (2#64)])=(none,post) at run
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const (2#64)]=some [.val (.word (2#64))] := by rfl
   have terminal:=evaluate_mptFail_call_terminal s (.const (2#64)) (2#64) code args
   rw [run] at terminal
   exact False.elim (terminal rfl)
 · have zeroRaw : kind≠0:=zero
   simp only [if_neg zero,if_pos rfl,evaluateHOLFiniteState_skip] at run
   exact ⟨zero,(Prod.mk.inj run).2.symm⟩

#print axioms mpt_insert_guard_normal_identity
end InitECandidate.Runtime

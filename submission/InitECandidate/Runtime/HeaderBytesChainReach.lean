import InitECandidate.Runtime.HeaderBytesStepReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def headerBytesChain (steps : List (BitVec 64 × BitVec 64 × Nat)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  match steps with
  | [] => continuation
  | (index,width,offset) :: rest => headerBytesStep index width offset (headerBytesChain rest continuation)

structure HeaderBytesFrame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record : BitVec 64) (ceiling : Nat) : Prop where
  table : RlpSliceInputPrefix post array input inputLength count.toNat
  locals : ∀ name : MlS, name ≠ ofString "f" → post.locals.lookup name = s.locals.lookup name
  domain : post.memaddrs = s.memaddrs
  code : post.code = s.code
  globals : ∀ name : MlS, post.globals.lookup name = s.globals.lookup name
  memory : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < record.toNat → post.memory address = s.memory address

/-- A concrete finite chain of actual field assignments/stores retains the
real table, workspace globals and older heap words, with one parser budget per entry. -/
theorem header_bytes_chain_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (steps : List (BitVec 64 × BitVec 64 × Nat)) (continuation : ProgHOL 64)
    (validSteps : ∀ item ∈ steps, item.1.toNat < count.toNat ∧ item.2.2 < 248)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : steps.length * (headerRlpFieldCost inputLimit + 1) ≤ s.clock) :
    Reaches s (headerBytesChain steps continuation)
      (fun post => HeaderBytesFrame s post array count input inputLength record ceiling)
      (steps.length * (headerRlpFieldCost inputLimit + 1)) continuation := by
  induction steps generalizing s with
  | nil =>
    exact Or.inl ⟨s,⟨table,fun _ _ => rfl,rfl,rfl,fun _ => rfl,fun _ _ _ => rfl⟩,by simp,le_refl _,scoped_refl _⟩
  | cons item rest ih =>
    obtain ⟨index,width,offset⟩ := item
    have valid := validSteps (index,width,offset) (by simp)
    have restValid : ∀ item ∈ rest, item.1.toNat < count.toNat ∧ item.2.2 < 248 := by
      intro item member
      exact validSteps item (by simp [member])
    have costEq : ((index,width,offset) :: rest).length * (headerRlpFieldCost inputLimit + 1) =
        (headerRlpFieldCost inputLimit + 1) + rest.length * (headerRlpFieldCost inputLimit + 1) := by
      simp only [List.length_cons,Nat.succ_mul]
      omega
    rw [costEq] at budget ⊢
    change Reaches s (headerBytesStep index width offset (headerBytesChain rest continuation)) _ _ _
    have first := header_bytes_step_reaches s array count input inputLength scratch frame record ceiling inputLimit index width offset
      (headerBytesChain rest continuation) valid.2 atArray atRecord before recordFits table valid.1 above fits inputBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
    have firstTimed : Reaches s (headerBytesStep index width offset (headerBytesChain rest continuation))
        (fun post => HeaderBytesFrame s post array count input inputLength record ceiling ∧
          s.clock ≤ post.clock + (headerRlpFieldCost inputLimit + 1))
        (headerRlpFieldCost inputLimit + 1) (headerBytesChain rest continuation) := by
      rcases first with ⟨post,facts,spent,remaining,agreement⟩ | aborted
      · obtain ⟨word,locals,tablePost,domain,installed,globals,memory⟩ := facts
        exact Or.inl ⟨post,⟨⟨tablePost,by
          intro name different
          rw [locals]
          simpa [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different],domain,installed,globals,memory⟩,spent⟩,spent,remaining,agreement⟩
      · exact Or.inr aborted
    apply reaches_trans s _ (headerBytesChain rest continuation) continuation _ _
      (headerRlpFieldCost inputLimit + 1) (rest.length * (headerRlpFieldCost inputLimit + 1)) firstTimed
    intro next facts
    obtain ⟨kept,spent⟩ := facts
    have tail := ih next restValid (by rw [kept.locals _ (by decide)]; exact atArray)
      (by rw [kept.locals _ (by decide)]; exact atRecord) kept.table
      (by rw [kept.globals]; exact scratchGlobal) (by rw [kept.globals]; exact frameGlobal)
      (kept.code.trans code) (by intro address lo hi; rw [kept.domain]; exact arena address lo hi) (by omega)
    apply reaches_mono next _ continuation _ _ _ _ (le_refl _) ?_ tail
    intro post framePost
    exact ⟨framePost.table,fun name different => (framePost.locals name different).trans (kept.locals name different),
      framePost.domain.trans kept.domain,framePost.code.trans kept.code,
      fun name => (framePost.globals name).trans (kept.globals name),
      fun address lo hi => (framePost.memory address lo hi).trans (kept.memory address lo hi)⟩

#print axioms header_bytes_chain_reaches
end InitECandidate.Runtime

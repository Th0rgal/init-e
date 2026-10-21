import InitECandidate.Runtime.SourceCostCrepWork
import InitECandidate.Runtime.SourceSiteMoves
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Executed Crep work indexed by the current function, with a call price per
(caller, callee, return-name count). Callee bodies run at the callee's index; `CrepWorkP` is
the constant-call-price instance. -/

/-- Crep function names. -/
abbrev CName := Flapjack.Basis.Pure.MlString.MlString

/-- Number of return names of a call. -/
def crepRetCount {α : Type} : Option (List Nat × α) → Nat
  | some (rts, _) => rts.length
  | none => 0

/-- Statement prices of Crep work: per statement kind, with argument, return
and primitive prices as functions of the actual counts, and a call exit split
into returned words, an unhandled exception and a handler dispatch. -/
structure StmtK where
  tick : Nat
  brk : Nat
  cont : Nat
  ffi : Nat
  raise : Nat
  storeGlob : Nat
  shMem : Nat
  store : Nat
  store32 : Nat
  ret : Nat → Nat
  prim : Nat → Nat → Nat
  ite : Nat
  wh : Nat
  argP : Nat → Nat
  retW : Nat
  exnP : Nat
  hdlP : Nat

/-- The exit charge of a call by its callee's result. -/
def StmtK.exit (K : StmtK) : Option (CrepResultHOLExact 64) → Nat
  | some (.return values) => K.retW * values.length
  | some (.exception _) => K.exnP
  | _ => 0

/-- The constant-price statement prices of `CrepWorkP` (its argument moves are in its list price). -/
def StmtK.uniform (unit prim ret : Nat) : StmtK where
  tick := unit
  brk := unit
  cont := unit
  ffi := unit
  raise := prim + 1
  storeGlob := unit
  shMem := unit
  store := unit
  store32 := unit
  ret := fun n => unit + n
  prim := fun a b => prim + a + b
  ite := unit
  wh := unit + unit + unit
  argP := fun _ => 0
  retW := ret
  exnP := ret * 3
  hdlP := ret

theorem StmtK.uniform_exit (unit prim ret : Nat) (r : Option (CrepResultHOLExact 64)) :
    (StmtK.uniform unit prim ret).exit r = ret * crepCallPayloadWords r := by
  rcases r with _ | r
  · rfl
  · cases r <;> simp [StmtK.exit, StmtK.uniform, crepCallPayloadWords, Nat.mul_comm]

/-- `callP caller callee n` prices a call with `n` return names; `shortP` is
charged by a call that stops before its callee runs. -/
inductive CrepWorkF (price : CrepExpHOL 64 → Nat) (priceList : List (CrepExpHOL 64) → Nat)
    (K : StmtK) (callP : CName → CName → Nat → Nat) (shortP : Nat) {σ : Type} :
    CName → CrepSemHOLState 64 σ → CrepProgHOL 64 → Nat → Prop where
  | skip (fn : CName) (t) : CrepWorkF price priceList K callP shortP fn t .skip 0
  | tick (fn : CName) (t) : CrepWorkF price priceList K callP shortP fn t .tick K.tick
  | breakStmt (fn : CName) (t label) : CrepWorkF price priceList K callP shortP fn t (.break label) K.brk
  | continueStmt (fn : CName) (t label) : CrepWorkF price priceList K callP shortP fn t (.continue label) K.cont
  | raise (fn : CName) (t code) : CrepWorkF price priceList K callP shortP fn t (.raise code) K.raise
  | assign (fn : CName) (t name value) : CrepWorkF price priceList K callP shortP fn t (.assign name value) (price value)
  | storeGlob (fn : CName) (t address value) :
      CrepWorkF price priceList K callP shortP fn t (.storeGlob address value) (K.storeGlob + price value)
  | store (fn : CName) (t address value) :
      CrepWorkF price priceList K callP shortP fn t (.store address value) (K.store + price address + price value)
  | store32 (fn : CName) (t address value) :
      CrepWorkF price priceList K callP shortP fn t (.store32 address value) (K.store32 + price address + price value)
  | storeByte (fn : CName) (t address value) :
      CrepWorkF price priceList K callP shortP fn t (.storeByte address value) (K.store32 + price address + price value)
  | returnStmt (fn : CName) (t values) :
      CrepWorkF price priceList K callP shortP fn t (.return values) (K.ret values.length + priceList values)
  | primitive (fn : CName) (t names operator args) :
      CrepWorkF price priceList K callP shortP fn t (.primitive names operator args) (K.prim names.length args.length)
  | shMem (fn : CName) (t operator name address) :
      CrepWorkF price priceList K callP shortP fn t (.shMem operator name address) (K.shMem + price address)
  | extCall (fn : CName) (t function configuration configurationLength array arrayLength) :
      CrepWorkF price priceList K callP shortP fn t (.extCall function configuration configurationLength array arrayLength) K.ffi
  | decFailure {fn : CName} {t name value body} (failed : evalCrepSemHOLExp t value = none) :
      CrepWorkF price priceList K callP shortP fn t (.dec name value body) (price value)
  | dec {fn : CName} {t name value body word bodyWork}
      (evaluated : evalCrepSemHOLExp t value = some word)
      (bodyRun : CrepWorkF price priceList K callP shortP fn { t with locals := t.locals.updateEq (name, word) } body bodyWork) :
      CrepWorkF price priceList K callP shortP fn t (.dec name value body) (price value + bodyWork)
  | seqNext {fn : CName} {t first second middle firstWork secondWork}
      (one : CrepWorkF price priceList K callP shortP fn t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (none, middle))
      (two : CrepWorkF price priceList K callP shortP fn middle second secondWork) :
      CrepWorkF price priceList K callP shortP fn t (.seq first second) (firstWork + secondWork)
  | seqStop {fn : CName} {t first second result middle firstWork}
      (one : CrepWorkF price priceList K callP shortP fn t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (some result, middle)) :
      CrepWorkF price priceList K callP shortP fn t (.seq first second) firstWork
  | iteBranch {fn : CName} {t condition yes no word branchWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word))
      (branch : CrepWorkF price priceList K callP shortP fn t (if word ≠ 0 then yes else no) branchWork) :
      CrepWorkF price priceList K callP shortP fn t (.ite condition yes no) (K.ite + price condition + branchWork)
  | iteInvalid {fn : CName} {t condition yes no}
      (invalid : ∀ word, evalCrepSemHOLExp t condition ≠ some (.word word)) :
      CrepWorkF price priceList K callP shortP fn t (.ite condition yes no) (K.ite + price condition)
  | whileExit {fn : CName} {t condition body}
      (exit : ∀ word, evalCrepSemHOLExp t condition = some (.word word) → word = 0) :
      CrepWorkF price priceList K callP shortP fn t (.while condition body) (K.wh + price condition)
  | whileTimeout {fn : CName} {t condition body word}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock = 0) :
      CrepWorkF price priceList K callP shortP fn t (.while condition body) (K.wh + price condition)
  | whileLoop {fn : CName} {t condition body word bodyWork result middle restWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkF price priceList K callP shortP fn (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (again : result = none ∨ result = some (.continue 0))
      (rest : CrepWorkF price priceList K callP shortP fn middle (.while condition body) restWork) :
      CrepWorkF price priceList K callP shortP fn t (.while condition body) (K.wh + price condition + bodyWork + restWork)
  | whileStop {fn : CName} {t condition body word bodyWork result middle}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkF price priceList K callP shortP fn (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (stop : result ≠ none ∧ result ≠ some (.continue 0)) :
      CrepWorkF price priceList K callP shortP fn t (.while condition body) (K.wh + price condition + bodyWork)
  /-- Argument failure, lookup failure, return-name rejection or timeout. -/
  | callShort {fn : CName} {t returnInfo function arguments}
      (short : arguments.mapM (evalCrepSemHOLExp t) = none ∨
        ∃ values, arguments.mapM (evalCrepSemHOLExp t) = some values ∧
          (lookupCodeFiniteHOL t.code function values values.length = none ∨
            crepReturnInfoNodupError returnInfo ∨ t.clock = 0)) :
      CrepWorkF price priceList K callP shortP fn t (.call returnInfo function arguments)
        (callP fn function (crepRetCount returnInfo) + shortP + priceList arguments + K.argP arguments.length)
  | callBody {fn : CName} {t returnInfo function arguments values body locals bodyWork result post}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : ¬ crepReturnInfoNodupError returnInfo)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkF price priceList K callP shortP function { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (result, post))
      (unhandled : ∀ code rts handler, result = some (.exception code) →
        returnInfo ≠ some (rts, some (code, handler))) :
      CrepWorkF price priceList K callP shortP fn t (.call returnInfo function arguments)
        (callP fn function (crepRetCount returnInfo) + priceList arguments + K.argP arguments.length + bodyWork +
          K.exit result)
  | callHandler {fn : CName} {t rts code handler function arguments values body locals bodyWork post
      handlerWork}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : rts.Nodup)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkF price priceList K callP shortP function { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (some (.exception code), post))
      (handlerRun : CrepWorkF price priceList K callP shortP fn { post with locals := t.locals } handler handlerWork) :
      CrepWorkF price priceList K callP shortP fn t (.call (some (rts, some (code, handler))) function arguments)
        (callP fn function rts.length + priceList arguments + K.argP arguments.length + bodyWork + K.hdlP + handlerWork)

section
variable {price : CrepExpHOL 64 → Nat} {priceList : List (CrepExpHOL 64) → Nat} {unit prim call ret : Nat}

theorem crepMapM_length {σ : Type} {t : CrepSemHOLState 64 σ} :
    ∀ {es : List (CrepExpHOL 64)} {vs : List (HolWordLab 64)}, es.mapM (evalCrepSemHOLExp t) = some vs → vs.length = es.length
  | [], vs, h => by simp at h; subst h; rfl
  | e :: es, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    rcases he : evalCrepSemHOLExp t e with _ | v <;> rw [he] at h <;> simp at h
    rcases hes : es.mapM (evalCrepSemHOLExp t) with _ | vs' <;> rw [hes] at h <;> simp at h
    subst h; simp [crepMapM_length hes]

/-- Constant-call-price work is indexed work, at no larger total, in every function. -/
theorem CrepWorkP.toF {σ : Type} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (work : CrepWorkP price priceList unit prim call ret t p w) :
    ∀ fn, ∃ w', CrepWorkF price priceList (StmtK.uniform unit prim ret) (fun _ _ _ => call) 0 fn t p w' ∧ w' ≤ w := by
  induction work with
  | skip t => intro fn; exact ⟨_, .skip fn t, Nat.le_refl _⟩
  | tick t => intro fn; exact ⟨_, .tick fn t, Nat.le_refl _⟩
  | breakStmt t l => intro fn; exact ⟨_, .breakStmt fn t l, Nat.le_refl _⟩
  | continueStmt t l => intro fn; exact ⟨_, .continueStmt fn t l, Nat.le_refl _⟩
  | raise t c => intro fn; exact ⟨_, .raise fn t c, Nat.le_refl _⟩
  | assign t n v => intro fn; exact ⟨_, .assign fn t n v, Nat.le_refl _⟩
  | storeGlob t a v => intro fn; exact ⟨_, .storeGlob fn t a v, Nat.le_refl _⟩
  | store t a v => intro fn; exact ⟨_, .store fn t a v, Nat.le_refl _⟩
  | store32 t a v => intro fn; exact ⟨_, .store32 fn t a v, Nat.le_refl _⟩
  | storeByte t a v => intro fn; exact ⟨_, .storeByte fn t a v, Nat.le_refl _⟩
  | returnStmt t vs => intro fn; exact ⟨_, .returnStmt fn t vs, by simp only [StmtK.uniform]; omega⟩
  | primitive t ns op as => intro fn; exact ⟨_, .primitive fn t ns op as, Nat.le_refl _⟩
  | shMem t op n a => intro fn; exact ⟨_, .shMem fn t op n a, Nat.le_refl _⟩
  | extCall t f a b c d => intro fn; exact ⟨_, .extCall fn t f a b c d, Nat.le_refl _⟩
  | decFailure failed => intro fn; exact ⟨_, .decFailure failed, Nat.le_refl _⟩
  | dec evaluated _ ih =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih fn; exact ⟨_, .dec evaluated k1, by omega⟩
  | seqNext _ run _ ih1 ih2 =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih1 fn; obtain ⟨w2, k2, b2⟩ := ih2 fn
    exact ⟨_, .seqNext k1 run k2, by omega⟩
  | seqStop _ run ih => intro fn; obtain ⟨w1, k1, b1⟩ := ih fn; exact ⟨_, .seqStop k1 run, b1⟩
  | iteBranch guard _ ih =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih fn; exact ⟨_, .iteBranch guard k1, by simp only [StmtK.uniform]; omega⟩
  | iteInvalid invalid => intro fn; exact ⟨_, .iteInvalid invalid, Nat.le_refl _⟩
  | whileExit exit => intro fn; exact ⟨_, .whileExit exit, Nat.le_refl _⟩
  | whileTimeout guard nonzero clock => intro fn; exact ⟨_, .whileTimeout guard nonzero clock, Nat.le_refl _⟩
  | whileLoop guard nonzero clock _ run again _ ih1 ih2 =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih1 fn; obtain ⟨w2, k2, b2⟩ := ih2 fn
    exact ⟨_, .whileLoop guard nonzero clock k1 run again k2, by simp only [StmtK.uniform]; omega⟩
  | whileStop guard nonzero clock _ run stop ih =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih fn
    exact ⟨_, .whileStop guard nonzero clock k1 run stop, by simp only [StmtK.uniform]; omega⟩
  | callShort short => intro fn; exact ⟨_, .callShort short, by simp only [StmtK.uniform]; omega⟩
  | @callBody t returnInfo function arguments values body locals bodyWork result post args lookup names clock
      _ run unhandled ih =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih function
    refine ⟨_, .callBody args lookup names clock k1 run unhandled, ?_⟩
    rw [StmtK.uniform_exit]; simp only [StmtK.uniform]; omega
  | @callHandler t rts code handler function arguments values body locals bodyWork post handlerWork args lookup
      names clock _ run _ ih1 ih2 =>
    intro fn; obtain ⟨w1, k1, b1⟩ := ih1 function; obtain ⟨w2, k2, b2⟩ := ih2 fn
    exact ⟨_, .callHandler args lookup names clock k1 run k2, by simp only [StmtK.uniform]; omega⟩

end

#print axioms StmtK.uniform_exit
#print axioms CrepWorkP.toF
end InitECandidate.Runtime.FineCost

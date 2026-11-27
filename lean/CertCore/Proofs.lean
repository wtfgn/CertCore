import CertCore.Check

/-!
# `CertCore.Proofs` — trusted

The T5 checker-soundness proof (M3.7) and the lemma layer it needs.

`check_sound` is stated with the program's initial-state invariant `hP : D.P
(State.init p)`: a generic domain has no way to prove its own `P` at the
program's initial state, and the interval instance supplies it via
`POn_init`. The checker itself establishes `Program.WF` and the certificate
shape.

Status: **M3.7 complete — T5 proved.**
-/

namespace CertCore

/-! ## Checker decomposition -/

/-- Every component of a successful check succeeded. -/
theorem check_parts {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    (h : check D p cert = .ok ()) :
    p.checkWF = true ∧ cert.wellFormed p = true ∧
    checkInit D p cert = .ok () ∧
    checkEdges D p cert = .ok () ∧
    checkSafety D p cert = .ok () := by
  unfold check at h
  by_cases hp : p.checkWF = true
  · simp [hp] at h
    by_cases hc : cert.wellFormed p = true
    · simp [hc] at h
      cases hi : checkInit D p cert with
      | error d => simp [hi] at h
      | ok u =>
          cases u
          simp [hi] at h
          cases he : checkEdges D p cert with
          | error d => simp [he] at h
          | ok u =>
              cases u
              simp [he] at h
              cases hs : checkSafety D p cert with
              | error d => simp [hs] at h
              | ok u =>
                  cases u
                  simp [hs] at h
                  exact ⟨hp, hc, by simp, by simp, by simp⟩
    · simp [hc] at h
  · simp [hp] at h

/-! ## Obligation projections -/

theorem checkInitFrom_ok {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    {ls : List Label} (h : checkInitFrom D p cert ls = .ok ()) :
    ∀ l, l ∈ ls →
      ∃ a, cert.stateAtEntry D cert.entry.point l = some a ∧
        D.ble (D.initOf p) a = true := by
  induction ls with
  | nil =>
      intro l hl
      simp at hl
  | cons l ls ih =>
      intro l' hl
      simp only [checkInitFrom] at h
      cases hsrc : cert.stateAtEntry D cert.entry.point l with
      | none =>
          simp only [hsrc] at h
          simp at h
      | some a =>
          simp only [hsrc] at h
          split at h
          · rename_i hble
            have htail : checkInitFrom D p cert ls = .ok () := by
              simpa using h
            rcases List.mem_cons.mp hl with rfl | hmem
            · exact ⟨a, hsrc, hble⟩
            · exact ih htail l' hmem
          · simp at h

theorem wellFormed_entry_label {Abs : Type} {p : Program} {cert : Certificate Abs}
    (h : cert.wellFormed p = true) : cert.entry.label < cert.labels := by
  have h' := h
  simp only [Certificate.wellFormed, Bool.and_eq_true, Nat.blt_eq,
    decide_eq_true_eq] at h'
  have hlabels : cert.labels = 1 := h'.1.1.1.1.1.1
  have hlt : cert.entry.label < cert.labels := h'.1.1.1.1.2
  omega

theorem wellFormed_entry_point {Abs : Type} {p : Program} {cert : Certificate Abs}
    (h : cert.wellFormed p = true) : cert.entry.point = p.entry := by
  have h' := h
  simp only [Certificate.wellFormed, Bool.and_eq_true, Nat.blt_eq,
    decide_eq_true_eq] at h'
  exact h'.1.1.1.2

theorem checkInit_entry {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    (h : checkInit D p cert = .ok ()) (hwf : cert.wellFormed p = true) :
    ∃ a, cert.stateAtEntry D cert.entry.point cert.entry.label = some a ∧
      D.ble (D.initOf p) a = true := by
  have hlt := wellFormed_entry_label (p := p) (cert := cert) hwf
  exact checkInitFrom_ok h cert.entry.label (List.mem_range.mpr hlt)

/-! ## Edge projections -/

theorem checkEdgeLabels_tail {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs} {e : Edge} {l : Label} {ls : List Label}
    (h : checkEdgeLabels D p cert e (l :: ls) = .ok ()) :
    checkEdgeLabels D p cert e ls = .ok () := by
  simp only [checkEdgeLabels] at h
  cases hs : cert.stateAtEntry D e.src l with
  | none => simpa [hs] using h
  | some a =>
      cases ht : cert.stateAtEntry D e.dst l with
      | none => simp [hs, ht] at h
      | some b =>
          simp only [hs, ht] at h
          split at h
          · simpa using h
          · simp at h

theorem checkEdgeLabels_head {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs} {e : Edge} {l : Label} {ls : List Label}
    (h : checkEdgeLabels D p cert e (l :: ls) = .ok ()) :
    ∀ a, cert.stateAtEntry D e.src l = some a →
      ∃ b, cert.stateAtEntry D e.dst l = some b ∧
        D.ble (D.transfer e.cmd a) b = true := by
  intro a hsrc
  simp only [checkEdgeLabels] at h
  cases hs : cert.stateAtEntry D e.src l with
  | none => simp [hs] at hsrc
  | some a0 =>
      simp only [hs] at h
      rw [hs] at hsrc
      cases hsrc
      cases ht : cert.stateAtEntry D e.dst l with
      | none => simp [ht] at h
      | some b =>
          simp only [ht] at h
          split at h
          · rename_i hble
            exact ⟨b, rfl, hble⟩
          · simp at h

theorem checkEdgeLabels_ok {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs} {e : Edge} {ls : List Label}
    (h : checkEdgeLabels D p cert e ls = .ok ()) :
    ∀ l, l ∈ ls → ∀ a, cert.stateAtEntry D e.src l = some a →
      ∃ b, cert.stateAtEntry D e.dst l = some b ∧
        D.ble (D.transfer e.cmd a) b = true := by
  induction ls with
  | nil =>
      intro l hl
      simp at hl
  | cons l ls ih =>
      intro l' hl a hsrc
      rcases List.mem_cons.mp hl with rfl | hmem
      · exact checkEdgeLabels_head h a hsrc
      · exact ih (checkEdgeLabels_tail h) l' hmem a hsrc

theorem checkEdgesFrom_ok {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs} {es : List Edge}
    (h : checkEdgesFrom D p cert es = .ok ()) :
    ∀ e, e ∈ es → ∀ l, l ∈ List.range cert.labels →
      ∀ a, cert.stateAtEntry D e.src l = some a →
        ∃ b, cert.stateAtEntry D e.dst l = some b ∧
          D.ble (D.transfer e.cmd a) b = true := by
  induction es with
  | nil =>
      intro e he
      simp at he
  | cons e es ih =>
      intro e' he' l hl a hsrc
      simp only [checkEdgesFrom] at h
      cases hhead : checkEdgeLabels D p cert e (List.range cert.labels) with
      | error d => simp [hhead] at h
      | ok u =>
          cases u
          simp only [hhead] at h
          rcases List.mem_cons.mp he' with rfl | hmem
          · exact checkEdgeLabels_ok hhead l hl a hsrc
          · exact ih (by simpa using h) e' hmem l hl a hsrc

theorem checkEdges_ok {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs}
    (h : checkEdges D p cert = .ok ()) :
    ∀ e, e ∈ (Program.compile p).edges → ∀ l, l ∈ List.range cert.labels →
      ∀ a, cert.stateAtEntry D e.src l = some a →
        ∃ b, cert.stateAtEntry D e.dst l = some b ∧
          D.ble (D.transfer e.cmd a) b = true :=
  checkEdgesFrom_ok h

/-! ## Safety projections -/

theorem checkSafetyLabels_tail {D : CertDomain} {cert : Certificate D.Abs}
    {instr : Instr} {point : Point} {l : Label} {ls : List Label}
    (h : checkSafetyLabels D cert instr point (l :: ls) = .ok ()) :
    checkSafetyLabels D cert instr point ls = .ok () := by
  simp only [checkSafetyLabels] at h
  cases hs : cert.stateAtEntry D point l with
  | none => simpa [hs] using h
  | some a =>
      simp only [hs] at h
      split at h
      · simpa using h
      · simp at h

theorem checkSafetyLabels_head {D : CertDomain} {cert : Certificate D.Abs}
    {instr : Instr} {point : Point} {l : Label} {ls : List Label}
    (h : checkSafetyLabels D cert instr point (l :: ls) = .ok ()) :
    ∀ a, cert.stateAtEntry D point l = some a →
      D.entails a (instrSafe instr) = true := by
  intro a hsrc
  simp only [checkSafetyLabels] at h
  cases hs : cert.stateAtEntry D point l with
  | none => simp [hs] at hsrc
  | some a0 =>
      simp only [hs] at h
      rw [hs] at hsrc
      cases hsrc
      split at h
      · rename_i hent
        exact hent
      · simp at h

theorem checkSafetyLabels_ok {D : CertDomain} {cert : Certificate D.Abs}
    {instr : Instr} {point : Point} {ls : List Label}
    (h : checkSafetyLabels D cert instr point ls = .ok ()) :
    ∀ l, l ∈ ls → ∀ a, cert.stateAtEntry D point l = some a →
      D.entails a (instrSafe instr) = true := by
  induction ls with
  | nil =>
      intro l hl
      simp at hl
  | cons l ls ih =>
      intro l' hl a hsrc
      rcases List.mem_cons.mp hl with rfl | hmem
      · exact checkSafetyLabels_head h a hsrc
      · exact ih (checkSafetyLabels_tail h) l' hmem a hsrc

theorem checkSafetyPoints_ok {D : CertDomain} {cert : Certificate D.Abs}
    {cfg : CFG} {pts : List Point}
    (h : checkSafetyPoints D cert cfg pts = .ok ()) :
    ∀ pt, pt ∈ pts → ∀ instr, cfg.instrAt pt = some instr →
      ∀ l, l ∈ List.range cert.labels →
        ∀ a, cert.stateAtEntry D pt l = some a →
          D.entails a (instrSafe instr) = true := by
  induction pts with
  | nil =>
      intro pt hpt
      simp at hpt
  | cons pt pts ih =>
      intro pt' hpt instr hi l hl a hsrc
      simp only [checkSafetyPoints] at h
      cases hinstr : cfg.instrAt pt with
      | none =>
          simp [hinstr] at h
          rcases List.mem_cons.mp hpt with rfl | hmem
          · rw [hi] at hinstr
            simp at hinstr
          · exact ih (by simpa using h) pt' hmem instr hi l hl a hsrc
      | some instr0 =>
          simp only [hinstr] at h
          cases hhead : checkSafetyLabels D cert instr0 pt
              (List.range cert.labels) with
          | error d => simp [hhead] at h
          | ok u =>
              cases u
              simp only [hhead] at h
              rcases List.mem_cons.mp hpt with rfl | hmem
              · rw [hi] at hinstr
                cases hinstr
                exact checkSafetyLabels_ok hhead l hl a hsrc
              · exact ih (by simpa using h) pt' hmem instr hi l hl a hsrc

theorem checkSafety_ok {D : CertDomain} {p : Program}
    {cert : Certificate D.Abs}
    (h : checkSafety D p cert = .ok ()) :
    ∀ pt, pt < (Program.compile p).instrs.size →
      ∀ instr, (Program.compile p).instrAt pt = some instr →
        ∀ l, l ∈ List.range cert.labels →
          ∀ a, cert.stateAtEntry D pt l = some a →
            D.entails a (instrSafe instr) = true := by
  intro pt hpt
  exact checkSafetyPoints_ok h pt (List.mem_range.mpr hpt)

/-! ## Semantic safety lemmas -/

theorem evalB_and_true {a b : BExp} {s : State}
    (h : evalB (.and a b) s = some true) :
    evalB a s = some true ∧ evalB b s = some true := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨x, hx, h2⟩
  rcases Option.bind_eq_some_iff.mp h2 with ⟨y, hy, hres⟩
  have hx' : x = true := by
    cases x <;> cases y <;> simp_all
  have hy' : y = true := by
    cases x <;> cases y <;> simp_all
  exact ⟨by simpa [hx'] using hx, by simpa [hy'] using hy⟩

theorem evalB_cmp_some {op : CmpOp} {l r : Expr} {s : State} {v : Bool}
    (h : evalB (.cmp op l r) s = some v) :
    ∃ a b, eval l s = some a ∧ eval r s = some b := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨a, ha, h2⟩
  rcases Option.bind_eq_some_iff.mp h2 with ⟨b, hb, _⟩
  exact ⟨a, b, ha, hb⟩

theorem evalB_not_some {b : BExp} {s : State} {v : Bool}
    (h : evalB (.not b) s = some v) : ∃ w, evalB b s = some w := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨w, hw, _⟩
  exact ⟨w, hw⟩

theorem evalB_or_some {a b : BExp} {s : State} {v : Bool}
    (h : evalB (.or a b) s = some v) :
    (∃ x, evalB a s = some x) ∧ (∃ y, evalB b s = some y) := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨x, hx, h2⟩
  rcases Option.bind_eq_some_iff.mp h2 with ⟨y, hy, _⟩
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

theorem compare_le_true {a b : I32} (h : compare .le a b = true) : a.val ≤ b.val := by
  simpa [compare] using h

theorem compare_lt_true {a b : I32} (h : compare .lt a b = true) : a.val < b.val := by
  simpa [compare] using h

theorem compare_eq_true {a b : I32} (h : compare .eq a b = true) : a.val = b.val := by
  simpa [compare] using h

theorem eval_len_val {a : Arr} {s : State} {n : I32}
    (h : eval (.len a) s = some n) : n.val = (s.memAt a).size := by
  simpa [eval] using I32.ofInt?_sound h

theorem evalB_cmp_true {op : CmpOp} {l r : Expr} {s : State}
    (h : evalB (.cmp op l r) s = some true) :
    ∃ a b, eval l s = some a ∧ eval r s = some b ∧ compare op a b = true := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨a, ha, h2⟩
  rcases Option.bind_eq_some_iff.mp h2 with ⟨b, hb, hres⟩
  exact ⟨a, b, ha, hb, by simpa using hres⟩

/-! ## Run invariant -/

/-- The abstract invariant at a point/label: a present abstract state whose
concretisation contains the concrete state. `bot`/missing is excluded at
reachable points (the edge obligations reject an edge into `bot`). -/
def CertInv (D : CertDomain) (cert : Certificate D.Abs) (label : Label)
    (pt : Point) (s : State) : Prop :=
  ∃ a, cert.stateAtEntry D pt label = some a ∧ D.gamma a s

theorem run_inv {D : CertDomain} {cert : Certificate D.Abs} {cfg : CFG}
    {label : Label}
    (hprog : ∀ pt s, pt < cfg.instrs.size → D.P s →
      CertInv D cert label pt s →
      ∃ q s', CFG.step cfg pt s = some (q, s') ∧ q < cfg.instrs.size ∧
        D.P s' ∧ CertInv D cert label q s') :
    ∀ n pt s, pt < cfg.instrs.size → D.P s →
      CertInv D cert label pt s →
      ∃ q s', CFG.run cfg n pt s = some (q, s') ∧ q < cfg.instrs.size ∧
        D.P s' ∧ CertInv D cert label q s' := by
  intro n
  induction n with
  | zero =>
      intro pt s hlt hP hinv
      exact ⟨pt, s, rfl, hlt, hP, hinv⟩
  | succ n ih =>
      intro pt s hlt hP hinv
      rcases hprog pt s hlt hP hinv with ⟨q, s', hstep, hq, hP', hinv'⟩
      rcases ih q s' hq hP' hinv' with ⟨q', s'', hrun, hq', hP'', hinv''⟩
      refine ⟨q', s'', ?_, hq', hP'', hinv''⟩
      simp [CFG.run, hstep, hrun]

/-- Every `I32` value has `|a| ≤ 2^31`. -/
private theorem natAbs_val_le_two_pow (a : I32) : (a.val.natAbs : Int) ≤ 2147483648 := by
  have hle : i32Min ≤ a.val := a.min_le
  have hge : a.val ≤ i32Max := a.le_max
  simp only [i32Min, i32Max] at hle hge
  rcases Int.lt_or_le a.val 0 with h | h
  · rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
    omega
  · rw [Int.natAbs_of_nonneg h]
    omega

/-- Truncating division by any `b` keeps the result inside `[-|a|, |a|]`. -/
private theorem tdiv_mem_natAbs (a b : Int) :
    -((a.natAbs : Int)) ≤ a.tdiv b ∧ a.tdiv b ≤ (a.natAbs : Int) := by
  have hle : (a.tdiv b).natAbs ≤ a.natAbs := Int.natAbs_tdiv_le_natAbs a b
  have hcast : (((a.tdiv b).natAbs : Nat) : Int) ≤ (a.natAbs : Int) := Int.ofNat_le.mpr hle
  have h1 : a.tdiv b ≤ (((a.tdiv b).natAbs : Nat) : Int) := Int.le_natAbs
  have h2 : -(a.tdiv b) ≤ (((a.tdiv b).natAbs : Nat) : Int) := by
    have h := Int.le_natAbs (a := -(a.tdiv b))
    simpa using h
  constructor
  · omega
  · omega

/-- `I32.div?` succeeds on every nonzero divisor except the single
`i32Min / -1` overflow case. -/
theorem div?_some_of_safe {a b : I32} (hb : b.val ≠ 0)
    (hmin : ¬(a.val = i32Min ∧ b.val = -1)) : (I32.div? a b).isSome := by
  rw [I32.div?_isSome_iff]
  have hle : i32Min ≤ a.val := a.min_le
  have hge : a.val ≤ i32Max := a.le_max
  simp only [i32Min, i32Max] at hle hge hmin ⊢
  have hmem := tdiv_mem_natAbs a.val b.val
  have hna := natAbs_val_le_two_pow a
  refine ⟨hb, ?_, ?_⟩
  · omega
  · by_cases ha : a.val = -2147483648
    · have ham : Int.natAbs (-2147483648) = 2147483648 := by decide
      by_cases hb1 : b.val.natAbs = 1
      · rcases Int.natAbs_eq_iff.mp hb1 with h | h
        · have h1 : b.val = 1 := by simpa using h
          rw [h1, Int.tdiv_one, ha]
          decide
        · exact absurd ⟨ha, h⟩ hmin
      · have hb0 : b.val.natAbs ≠ 0 := by simpa using hb
        have hb2 : 2 ≤ b.val.natAbs := by omega
        have hnat : (Int.tdiv a.val b.val).natAbs ≤ 2147483647 := by
          rw [Int.natAbs_tdiv, ha, ham]
          have hlt : 2147483648 / b.val.natAbs < 2147483648 :=
            Nat.div_lt_self (n := 2147483648) (k := b.val.natAbs) (by decide) hb2
          exact Nat.lt_succ_iff.mp hlt
        have hcast : (((Int.tdiv a.val b.val).natAbs : Nat) : Int) ≤ 2147483647 :=
          Int.ofNat_le.mpr hnat
        have h1 : Int.tdiv a.val b.val ≤ (((Int.tdiv a.val b.val).natAbs : Nat) : Int) :=
          Int.le_natAbs
        omega
    · have hna' : ((a.val.natAbs : Nat) : Int) ≤ 2147483647 := by
        rcases Int.lt_or_le a.val 0 with h | h
        · rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
          omega
        · rw [Int.natAbs_of_nonneg h]
          omega
      omega

theorem compare_ne_true {a b : I32} (h : compare .ne a b = true) : a.val ≠ b.val := by
  simpa [compare] using h

theorem evalB_not_true {b : BExp} {s : State}
    (h : evalB (.not b) s = some true) : evalB b s = some false := by
  simp only [evalB] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨w, hw, hres⟩
  have hw' : w = false := by simpa using hres
  simpa [hw'] using hw

theorem exprSafe_sound : ∀ (e : Expr) (s : State),
    evalB (exprSafe e) s = some true → ∃ v, eval e s = some v
  | .const n, s, _ => ⟨n, rfl⟩
  | .var x, s, _ => ⟨s.get x, rfl⟩
  | .add l r, s, h => by
      simp only [exprSafe] at h
      rcases evalB_and_true h with ⟨_, h2⟩
      rcases evalB_and_true h2 with ⟨_, heq⟩
      rcases evalB_cmp_some heq with ⟨v, _, hv, _⟩
      exact ⟨v, hv⟩
  | .sub l r, s, h => by
      simp only [exprSafe] at h
      rcases evalB_and_true h with ⟨_, h2⟩
      rcases evalB_and_true h2 with ⟨_, heq⟩
      rcases evalB_cmp_some heq with ⟨v, _, hv, _⟩
      exact ⟨v, hv⟩
  | .mul l r, s, h => by
      simp only [exprSafe] at h
      rcases evalB_and_true h with ⟨_, h2⟩
      rcases evalB_and_true h2 with ⟨_, heq⟩
      rcases evalB_cmp_some heq with ⟨v, _, hv, _⟩
      exact ⟨v, hv⟩
  | .div l r, s, h => by
      simp only [exprSafe] at h
      rcases evalB_and_true h with ⟨hl, h2⟩
      rcases evalB_and_true h2 with ⟨hr, h3⟩
      rcases evalB_and_true h3 with ⟨hne, hnot⟩
      rcases exprSafe_sound l s hl with ⟨a, ha⟩
      rcases exprSafe_sound r s hr with ⟨b, hb⟩
      rcases evalB_cmp_true hne with ⟨b2, z, hb2, hz, hneTrue⟩
      have hb2eq : b2 = b := eval_det hb2 hb
      subst b2
      have hz0 : z = I32.zero := by
        exact eval_det hz rfl
      subst z
      have hbne : b.val ≠ 0 := by
        simpa [I32.zero] using compare_ne_true hneTrue
      have hmin : ¬(a.val = i32Min ∧ b.val = -1) := by
        rintro ⟨haMin, hbMin⟩
        have hinner : evalB (safeAnd (.cmp .eq l (.const I32.min))
            (.cmp .eq r (.const (I32.ofIntWrap (-1))))) s = some true := by
          simp [safeAnd, evalB, ha, hb, compare, haMin, hbMin, I32.min,
            I32.ofIntWrap]
        have hfalse := evalB_not_true hnot
        rw [hinner] at hfalse
        cases hfalse
      rcases Option.isSome_iff_exists.mp (div?_some_of_safe hbne hmin) with ⟨v, hv⟩
      exact ⟨v, by simp [eval, ha, hb, hv]⟩
  | .read a i, s, h => by
      simp only [exprSafe] at h
      rcases evalB_and_true h with ⟨_, h2⟩
      rcases evalB_and_true h2 with ⟨hlo, hhi⟩
      rcases evalB_cmp_true hlo with ⟨z, idx, hz, hi, hle⟩
      rcases evalB_cmp_true hhi with ⟨idx2, len, hi2, hlen, hlt⟩
      have hidx : idx2 = idx := eval_det hi2 hi
      subst idx2
      have hz0 : z = I32.zero := eval_det hz rfl
      subst z
      have hsize := eval_len_val hlen
      have hlo' : 0 ≤ idx.val := by simpa [I32.zero] using compare_le_true hle
      have hhi' : idx.val < (s.memAt a).size := by
        have hlt' := compare_lt_true hlt
        simpa [hsize] using hlt'
      refine ⟨(s.memAt a).getD idx.val.toNat I32.zero, ?_⟩
      simp [eval, hi, hlo', hhi']
  | .len a, s, h => by
      simp only [exprSafe] at h
      rcases evalB_cmp_some h with ⟨v, _, hv, _⟩
      exact ⟨v, hv⟩

theorem bexpDefined_sound : ∀ (b : BExp) (s : State),
    evalB (bexpDefined b) s = some true → ∃ v, evalB b s = some v
  | .cmp op l r, s, h => by
      simp only [bexpDefined] at h
      rcases evalB_and_true h with ⟨hl, hr⟩
      rcases exprSafe_sound l s hl with ⟨a, ha⟩
      rcases exprSafe_sound r s hr with ⟨b, hb⟩
      exact ⟨compare op a b, by simp [evalB, ha, hb]⟩
  | .not b, s, h => by
      simp only [bexpDefined] at h
      rcases bexpDefined_sound b s h with ⟨w, hw⟩
      exact ⟨!w, by simp [evalB, hw]⟩
  | .and l r, s, h => by
      simp only [bexpDefined] at h
      rcases evalB_and_true h with ⟨hl, hr⟩
      rcases bexpDefined_sound l s hl with ⟨x, hx⟩
      rcases bexpDefined_sound r s hr with ⟨y, hy⟩
      exact ⟨x && y, by simp [evalB, hx, hy]⟩
  | .or l r, s, h => by
      simp only [bexpDefined] at h
      rcases evalB_and_true h with ⟨hl, hr⟩
      rcases bexpDefined_sound l s hl with ⟨x, hx⟩
      rcases bexpDefined_sound r s hr with ⟨y, hy⟩
      exact ⟨x || y, by simp [evalB, hx, hy]⟩

theorem atomicSafe_sound : ∀ (cmd : AtomicCmd) (s : State),
    evalB (atomicSafe cmd) s = some true → ∃ s', CFG.exec cmd s = some s'
  | .skip, s, _ => ⟨s, rfl⟩
  | .assign x e, s, h => by
      simp only [atomicSafe] at h
      rcases exprSafe_sound e s h with ⟨v, hv⟩
      exact ⟨s.set x v, by simp [CFG.exec, hv]⟩
  | .store a i v, s, h => by
      simp only [atomicSafe] at h
      rcases evalB_and_true h with ⟨hiSafe, h2⟩
      rcases evalB_and_true h2 with ⟨hvSafe, h3⟩
      rcases evalB_and_true h3 with ⟨hlo, hhi⟩
      rcases exprSafe_sound i s hiSafe with ⟨idx, hidx⟩
      rcases exprSafe_sound v s hvSafe with ⟨val, hval⟩
      rcases evalB_cmp_true hlo with ⟨z, idx2, hz, hidx2, hle⟩
      rcases evalB_cmp_true hhi with ⟨idx3, len, hidx3, hlen, hlt⟩
      have hz0 : z = I32.zero := eval_det hz rfl
      subst z
      have hidx2' : idx2 = idx := eval_det hidx2 hidx
      subst idx2
      have hidx3' : idx3 = idx := eval_det hidx3 hidx
      subst idx3
      have hsize := eval_len_val hlen
      have hlo' : 0 ≤ idx.val := by simpa [I32.zero] using compare_le_true hle
      have hhi' : idx.val < (s.memAt a).size := by
        have hlt' := compare_lt_true hlt
        simpa [hsize] using hlt'
      refine ⟨s.setMem a ((s.memAt a).set idx.val.toNat val), ?_⟩
      simp [CFG.exec, hidx, hval, hlo', hhi']
  | .assert b, s, h => by
      simp only [atomicSafe] at h
      exact ⟨s, by simp [CFG.exec, h]⟩

theorem instrSafe_step {cfg : CFG} {p : Point} {instr : Instr} {s : State}
    (hi : cfg.instrAt p = some instr)
    (hsafe : evalB (instrSafe instr) s = some true) :
    ∃ q s', CFG.step cfg p s = some (q, s') := by
  cases instr with
  | atomic cmd next =>
      rcases atomicSafe_sound cmd s hsafe with ⟨s', hs'⟩
      exact ⟨next, s', by simp [CFG.step, hi, hs']⟩
  | branch b t e =>
      rcases bexpDefined_sound b s hsafe with ⟨v, hv⟩
      exact ⟨if v then t else e, s, by simp [CFG.step, hi, hv]⟩

theorem instrAt_some_of_lt {cfg : CFG} {p : Point} (h : p < cfg.instrs.size) :
    ∃ i, cfg.instrAt p = some i := by
  refine ⟨cfg.instrs[p], ?_⟩
  simp [CFG.instrAt, h]

/-- The run invariant plus the checker obligations give a successful,
invariant-preserving step. -/
theorem step_progress {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    (hEdges : checkEdges D p cert = .ok ())
    (hSafety : checkSafety D p cert = .ok ())
    (hlabel : cert.entry.label ∈ List.range cert.labels) :
    ∀ pt s, pt < (Program.compile p).instrs.size → D.P s →
      CertInv D cert cert.entry.label pt s →
      ∃ q s', CFG.step (Program.compile p) pt s = some (q, s') ∧
        q < (Program.compile p).instrs.size ∧ D.P s' ∧
        CertInv D cert cert.entry.label q s' := by
  intro pt s hlt hPs hinv
  rcases hinv with ⟨a, hstate, hgamma⟩
  rcases instrAt_some_of_lt hlt with ⟨instr, hi⟩
  have hsafe := checkSafety_ok hSafety pt hlt instr hi cert.entry.label hlabel a hstate
  have hent := D.entails_sound hsafe hPs hgamma
  rcases instrSafe_step hi hent with ⟨q, s', hstep⟩
  rcases CFG.step_edge hstep with ⟨e, he, hsrc, hdst, hexec⟩
  have hsrcState : cert.stateAtEntry D e.src cert.entry.label = some a := by
    rw [hsrc]
    exact hstate
  rcases checkEdges_ok hEdges e he cert.entry.label hlabel a hsrcState with
    ⟨b, htarget, hble⟩
  have hPs' := D.P_step hPs hexec
  have htrans := D.transfer_sound hPs hgamma hexec hPs'
  have hb := D.ble_sound hble hPs' htrans
  have hq : q < (Program.compile p).instrs.size := by
    have := (Program.compile_wf p).edges_dst_lt e he
    simpa [hdst] using this
  refine ⟨q, s', hstep, hq, hPs', ?_⟩
  refine ⟨b, ?_, hb⟩
  rw [← hdst]
  exact htarget

/-- The entry state is in the invariant: the init obligation at the entry label
plus domain init soundness. -/
theorem init_inv {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    (hcert : cert.wellFormed p = true)
    (hInit : checkInit D p cert = .ok ()) (hP : D.P (State.init p)) :
    CertInv D cert cert.entry.label (Program.compile p).entry (State.init p) := by
  have hentry : cert.entry.point = p.entry := wellFormed_entry_point (p := p) (cert := cert) hcert
  have hcfg : (Program.compile p).entry = cert.entry.point := by
    show p.entry = cert.entry.point
    exact hentry.symm
  rcases checkInit_entry hInit hcert with ⟨a, hstate, hble⟩
  have hinit := D.init_sound p hP
  have hgamma := D.ble_sound hble hP hinit
  refine ⟨a, ?_, hgamma⟩
  rw [hcfg]
  exact hstate

/-- **T5 — checker soundness.** A successfully checked certificate implies the
program is safe, given the domain's initial-state invariant. -/
theorem check_sound {D : CertDomain} {p : Program} {cert : Certificate D.Abs}
    (hP : D.P (State.init p)) (h : check D p cert = .ok ()) :
    Program.safe p := by
  rcases check_parts h with ⟨hpWF, hcert, hInit, hEdges, hSafety⟩
  have hlabel : cert.entry.label ∈ List.range cert.labels :=
    List.mem_range.mpr (wellFormed_entry_label (p := p) (cert := cert) hcert)
  let cfg := Program.compile p
  have hprog := step_progress (D := D) (p := p) (cert := cert) hEdges hSafety hlabel
  have hinitInv := init_inv (D := D) (p := p) (cert := cert) hcert hInit hP
  refine ⟨?_, ?_⟩
  · simpa [Program.WF] using hpWF
  · intro n
    rcases run_inv hprog n cfg.entry (State.init p) (Program.compile_wf p).1 hP
      hinitInv with ⟨q, s', hrun, hq, hP', hinv⟩
    rw [hrun]
    simp

end CertCore

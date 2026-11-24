import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.TopForm

-- All three circuit traversals append one entry per gate.
private def scan {α : Type} (step : List α → Gate → α)
    (gates : List Gate) (init : List α) : List α :=
  gates.foldl (fun acc gate => acc ++ [step acc gate]) init

private theorem scan_append {α : Type} (step : List α → Gate → α)
    (pre post : List Gate) (init : List α) :
    scan step (pre ++ post) init = scan step post (scan step pre init) :=
  List.foldl_append

private theorem scan_length {α : Type} (step : List α → Gate → α)
    (gates : List Gate) (init : List α) :
    (scan step gates init).length = init.length + gates.length := by
  induction gates generalizing init with
  | nil => simp [scan]
  | cons g gs ih =>
    simpa [scan, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (init ++ [step init g])

private theorem scan_get_init {α : Type} (step : List α → Gate → α) (gates : List Gate)
    (init : List α) (default : α) (i : ℕ) (hi : i < init.length) :
    (scan step gates init).getD i default = init.getD i default := by
  induction gates generalizing init with
  | nil => rfl
  | cons g gs ih =>
    exact (ih (init ++ [step init g]) (by simp; omega)).trans
      (by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi])

private theorem scan_get_gate {α : Type} (step : List α → Gate → α)
    (gates : List Gate) (init : List α) (default : α) (j : ℕ) (hj : j < gates.length) :
    (scan step gates init).getD (init.length + j) default =
      step (scan step (gates.take j) init) gates[j] := by
  have split : gates = (gates.take j ++ [gates[j]]) ++ gates.drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj, List.take_append_drop]
  have hlen : (scan step (gates.take j) init).length = init.length + j := by
    simp [scan_length, Nat.min_eq_left hj.le]
  calc
    _ = (scan step (gates.take j ++ [gates[j]]) init).getD (init.length + j) default := by
      conv_lhs => rw [split, scan_append]
      exact scan_get_init step _ _ _ (init.length + j) (by
        rw [scan_length, List.length_append, List.length_singleton, List.length_take,
          Nat.min_eq_left hj.le]
        omega)
    _ = _ := by
      rw [show scan step (gates.take j ++ [gates[j]]) init =
          scan step (gates.take j) init ++ [step (scan step (gates.take j) init) gates[j]] by
        rw [scan_append]; rfl, ← hlen]
      simp [List.getD_eq_getElem?_getD]

private theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

private theorem wire_of_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    wireVal n C u.val x = x u := by
  unfold wireVal
  change (scan (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x)).getD u.val false = x u
  rw [scan_get_init _ _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, u.isLt]

private theorem wire_out_of_range {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal n C w x = false := by
  unfold wireVal
  change (scan (fun acc g => g.op.eval (g.inputs.map fun i => acc.getD i false))
    C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [scan_length] using hw)

private theorem wire_of_gate {n : ℕ} {C : Circuit} (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => readVal n C j w x) := by
  let step := fun (acc : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => acc.getD i false)
  let pre := scan step (C.gates.take j) (List.ofFn x)
  have hlen : pre.length = n + j := by simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hgate := scan_get_gate step C.gates (List.ofFn x) false j hj
  rw [List.length_ofFn, ← gateAt_eq hj] at hgate
  change (scan step C.gates (List.ofFn x)).getD (n + j) false = _
  rw [hgate]
  apply congrArg (GateOp.eval (gateAt C j).op)
  apply List.map_congr_left
  intro w _
  change pre.getD w false = if w < n + j then
    (scan step C.gates (List.ofFn x)).getD w false else false
  split_ifs with hw
  · conv_rhs => rw [← List.take_append_drop j C.gates, scan_append]
    exact (scan_get_init step _ _ _ w (by rwa [hlen])).symm
  · exact List.getD_eq_default _ _ (by rw [hlen]; omega)

private theorem or_gate_iff {n : ℕ} {C : Circuit} (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = .or) :
    wireVal n C (n + j) x = true ↔
      ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ wireVal n C w x = true := by
  simp [wire_of_gate x hj, hop, GateOp.eval, readVal, List.any_eq_true]

private theorem and_gate_iff {n : ℕ} {C : Circuit} (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = .and) :
    wireVal n C (n + j) x = true ↔
      ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ wireVal n C w x = true := by
  simp [wire_of_gate x hj, hop, GateOp.eval, readVal, List.all_eq_true]

private theorem wire_mono {n : ℕ} {C : Circuit} (hops : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro htrue
    by_cases hw : w < n
    · let i : Fin n := ⟨w, hw⟩
      exact (wire_of_input C y i).trans (hxy i ((wire_of_input C x i).symm.trans htrue))
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · rcases hops (gateAt C j) (gateAt_eq hj ▸ List.getElem_mem hj) with hand | hor
        · apply (and_gate_iff y hj hand).2
          intro v hv
          obtain ⟨hlt, ht⟩ := (and_gate_iff x hj hand).1 htrue v hv
          exact ⟨hlt, ih v hlt ht⟩
        · obtain ⟨v, hv, hlt, ht⟩ := (or_gate_iff x hj hor).1 htrue
          exact (or_gate_iff y hj hor).2 ⟨v, hv, hlt, ih v hlt ht⟩
      · rw [wire_out_of_range C x _ (by omega)] at htrue
        contradiction

private def ClosedUnderOr (n : ℕ) (C : Circuit) (S : Set ℕ) : Prop :=
  ∀ i : Fin C.gates.length, n + i.val ∈ S → (C.gates.get i).op = .or →
    ∀ a ∈ (C.gates.get i).inputs, a ∈ S

private theorem true_or_atom {n : ℕ} {C : Circuit} (hops : AndOrOnly C) (x : Fin n → Bool) :
    ∀ w, wireVal n C w x = true →
      ∃ Y, (∀ S : Set ℕ, w ∈ S → ClosedUnderOr n C S → Y ∈ S) ∧
        wireVal n C Y x = true ∧
        (∀ y : Fin n → Bool, wireVal n C Y y = true → wireVal n C w y = true) ∧
        (Y < n ∨ ∃ i : Fin C.gates.length, Y = n + i.val ∧ (C.gates.get i).op = .and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · exact ⟨w, fun _ h _ => h, hw, fun _ h => h, Or.inl hin⟩
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases hj : j < C.gates.length
    · have hreal := gateAt_eq hj
      rcases hops (gateAt C j) (hreal ▸ List.getElem_mem hj) with hand | hor
      · exact ⟨n + j, fun _ h _ => h, hw, fun _ h => h,
          Or.inr ⟨⟨j, hj⟩, rfl, by change C.gates[j].op = .and; exact hreal ▸ hand⟩⟩
      · obtain ⟨v, hv, hlt, ht⟩ := (or_gate_iff x hj hor).1 hw
        obtain ⟨Y, hpath, htrue, hcarry, hatom⟩ := ih v hlt ht
        refine ⟨Y, ?_, htrue, ?_, hatom⟩
        · intro S hs hclosed
          have hop : (C.gates.get ⟨j, hj⟩).op = .or := by
            change C.gates[j].op = .or
            exact hreal ▸ hor
          have hmem : v ∈ (C.gates.get ⟨j, hj⟩).inputs := by
            change v ∈ C.gates[j].inputs
            exact hreal ▸ hv
          exact hpath S (hclosed ⟨j, hj⟩ hs hop v hmem) hclosed
        · intro y hy
          exact (or_gate_iff y hj hor).2 ⟨v, hv, hlt, hcarry y hy⟩
    · rw [wire_out_of_range C x _ (by omega)] at hw
      contradiction

private theorem line_intersection :
    ∀ t : Fin 13, t ≠ 0 →
      (({0, 1, 3, 9} : Finset (Fin 13)) ∩ {t, t + 1, t + 3, t + 9}).card ≤ 1 := by
  decide

private theorem eq_false_of_imp {a b : Bool} (hb : b = false) (h : a = true → b = true) :
    a = false := by
  cases a
  · rfl
  · exact Bool.noConfusion (hb.symm.trans (h rfl))

end PEqualNP.Outside.L_meta_1577

open PEqualNP.Outside.L_meta_1577 PEqualNP.CircuitLowerBounds
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_1577 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  intro L hL gates g t hlegal _ ht hg0 hgt hcount
  let C : Circuit := ⟨gates, g⟩
  let outside (r : Fin 13) : Fin 13 → Bool := fun v => decide (v ∉ L r)
  let test (p : Fin 13) : Fin 13 → Bool :=
    fun v => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0))
  let fired := (L 0).filter (fun p => wireVal 13 C g (test p) = true)
  have hops : AndOrOnly C := fun a ha => (hlegal a ha).1
  change wireVal 13 C g (outside 0) = false at hg0
  change wireVal 13 C g (outside t) = false at hgt
  change 2 ≤ fired.card at hcount
  have hmeet : (L 0 ∩ L t).card ≤ 1 := by
    rw [hL 0, hL t]
    exact line_intersection t ht
  have hex : ∃ p ∈ fired, p ∉ L t := by
    by_contra hn
    have hs : fired ⊆ L 0 ∩ L t := by
      intro p hp
      refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
      by_contra hpt
      exact hn ⟨p, hp, hpt⟩
    exact (by omega : ¬ fired.card ≤ (L 0 ∩ L t).card) (Finset.card_le_card hs)
  obtain ⟨s, hs, hst⟩ := hex
  have hsTrue : wireVal 13 C g (test s) = true := (Finset.mem_filter.mp hs).2
  have hsSpecial : s = 3 ∨ s = 9 := by
    by_contra hn
    have hsub : ∀ v, test s v = true → outside t v = true := by
      intro v hv
      have hv' : v = s := by simpa [test, hn] using hv
      simp [outside, hv', hst]
    exact Bool.noConfusion (hgt.symm.trans (wire_mono hops hsub g hsTrue))
  obtain ⟨Y, hpath, htest, hcarry, hatom⟩ := true_or_atom hops (test s) g hsTrue
  have hY0 := eq_false_of_imp hg0 (hcarry (outside 0))
  have hYt := eq_false_of_imp hgt (hcarry (outside t))
  rcases hatom with hinput | hAnd
  · let i : Fin 13 := ⟨Y, hinput⟩
    change wireVal 13 C i.val (outside 0) = false at hY0
    change wireVal 13 C i.val (outside t) = false at hYt
    change wireVal 13 C i.val (test s) = true at htest
    rw [wire_of_input] at hY0 hYt htest
    have hmem0 : i ∈ L 0 := by simpa [outside] using hY0
    have hmemt : i ∈ L t := by simpa [outside] using hYt
    have his : i = s := (of_decide_eq_true htest).resolve_right (fun h => h.2 hmem0)
    exact (hst (his ▸ hmemt)).elim
  · exact ⟨Y, hpath, hAnd, hY0, hYt, s, hsSpecial, hst, htest⟩

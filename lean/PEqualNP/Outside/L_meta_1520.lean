import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1520

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def base : Finset (Fin 13) := {0, 1, 3}

def zeroSet (x : Fin 13 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => x v = false)

def fromZeros (s : Finset (Fin 13)) (v : Fin 13) : Bool := decide (v ∉ s)

abbrev atBase (x : Fin 13 → Bool) : Prop := ∃ v ∈ base, x v = true

abbrev inLine (x : Fin 13 → Bool) : Prop :=
  ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ line s

def lineSupports : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion (fun t : Fin 13 => (line t).powerset)

def firstInput : Fin 13 → Bool := fromZeros (line 0)

def secondInput (v : Fin 13) : Bool := decide (v ∉ line 0 ∨ v = 9)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
lemma lineSupports_card : lineSupports.card = 157 := by decide +kernel

lemma base_line_unique : ∀ t : Fin 13, base ⊆ line t → t = 0 := by decide +kernel

lemma line_zero : line 0 = insert 9 base := by decide +kernel

lemma secondInput_eq : secondInput = fromZeros base := by decide +kernel

lemma first_ne_second : firstInput ≠ secondInput := by decide +kernel

lemma mem_zeroSet (x : Fin 13 → Bool) (v : Fin 13) :
    v ∈ zeroSet x ↔ x v = false := by
  simp [zeroSet]

lemma zeroSet_fromZeros (s : Finset (Fin 13)) : zeroSet (fromZeros s) = s :=
  Finset.ext (fun v => by simp [mem_zeroSet, fromZeros])

lemma fromZeros_zeroSet (x : Fin 13 → Bool) : fromZeros (zeroSet x) = x :=
  funext (fun v => by simp [fromZeros, mem_zeroSet])

lemma inLine_iff (x : Fin 13 → Bool) : inLine x ↔ zeroSet x ∈ lineSupports := by
  simp [lineSupports, Finset.subset_iff, mem_zeroSet]

lemma noBase_iff (x : Fin 13 → Bool) : ¬ atBase x ↔ base ⊆ zeroSet x := by
  simp [Finset.subset_iff, mem_zeroSet, not_and]

lemma first_inLine : inLine firstInput := by decide +kernel

lemma second_inLine : inLine secondInput := by decide +kernel

lemma first_noBase : ¬ atBase firstInput := by decide +kernel

lemma second_noBase : ¬ atBase secondInput := by decide +kernel

def fixedBits (v : Fin 13) : Finset Bool :=
  if v ∈ base then {false} else Finset.univ

lemma mem_fixedBits (b : Bool) (v : Fin 13) :
    b ∈ fixedBits v ↔ v ∈ base → b = false :=
  if h : v ∈ base then
    by simp [fixedBits, h]
  else
    by simp [fixedBits, h]

lemma fixedBits_prod : Finset.prod Finset.univ (fun v => (fixedBits v).card) = 1024 := by
  decide +kernel

lemma inLine_card : (Finset.univ.filter inLine).card = 157 :=
  (Finset.card_nbij' zeroSet fromZeros
    (fun x hx => (inLine_iff x).mp (Finset.mem_filter.mp hx).2)
    (fun s hs => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (inLine_iff _).mpr
        (by simpa only [zeroSet_fromZeros] using (show s ∈ lineSupports from hs))⟩)
    (fun x _ => fromZeros_zeroSet x)
    (fun s _ => zeroSet_fromZeros s)).trans lineSupports_card

lemma fixedBits_eq :
    (Finset.univ.filter (fun x => ¬ atBase x)) = Fintype.piFinset fixedBits :=
  Finset.ext fun x => calc
    x ∈ Finset.univ.filter (fun y => ¬ atBase y) ↔ ¬ atBase x := by simp
    _ ↔ ∀ v, v ∈ base → x v = false :=
      (noBase_iff x).trans (by simp [Finset.subset_iff, mem_zeroSet])
    _ ↔ x ∈ Fintype.piFinset fixedBits := by simp [Fintype.mem_piFinset, mem_fixedBits]

lemma not_base_card : (Finset.univ.filter (fun x => ¬ atBase x)).card = 1024 :=
  (congrArg Finset.card fixedBits_eq).trans ((Fintype.card_piFinset _).trans fixedBits_prod)

lemma base_card : (Finset.univ.filter atBase).card = 7168 :=
  Nat.eq_sub_of_add_eq (calc
    (Finset.univ.filter atBase).card + 1024 = (Finset.univ : Finset (Fin 13 → Bool)).card :=
      not_base_card ▸ Finset.card_filter_add_card_filter_not (s := Finset.univ) atBase
    _ = 8192 := Fintype.card_pi_const Bool 13)

lemma zeroSet_cases (s : Finset (Fin 13)) (hBase : base ⊆ s) (hLine : s ⊆ line 0) :
    s = line 0 ∨ s = base :=
  if h : (9 : Fin 13) ∈ s then
    Or.inl (Finset.Subset.antisymm hLine (line_zero.symm ▸ Finset.insert_subset h hBase))
  else
    Or.inr (Finset.Subset.antisymm
      (fun {v} hv =>
        have hInserted : v ∈ insert (9 : Fin 13) base := line_zero ▸ hLine hv
        (Finset.mem_insert.mp hInserted).resolve_left (fun hv9 => h (hv9 ▸ hv))) hBase)

lemma inLine_without_base (x : Fin 13 → Bool) (hNoBase : ¬ atBase x) (hx : inLine x) :
    x = firstInput ∨ x = secondInput :=
  match hx with
  | ⟨t, ht⟩ =>
    have hBase := (noBase_iff x).mp hNoBase
    have hLine : zeroSet x ⊆ line t := fun {v} hv => ht v ((mem_zeroSet x v).mp hv)
    have ht0 := base_line_unique t (hBase.trans hLine)
    (zeroSet_cases _ hBase (ht0 ▸ hLine)).elim
      (fun h => Or.inl ((fromZeros_zeroSet x).symm.trans (congrArg fromZeros h)))
      (fun h => Or.inr ((fromZeros_zeroSet x).symm.trans
        ((congrArg fromZeros h).trans secondInput_eq.symm)))

lemma domain_iff (x : Fin 13 → Bool) :
    (atBase x ∨ inLine x) ↔ (atBase x ∨ x = firstInput ∨ x = secondInput) :=
  ⟨fun h => h.elim Or.inl fun hx =>
    if hAt : atBase x then Or.inl hAt else Or.inr (inLine_without_base x hAt hx),
   fun h => h.elim Or.inl fun hx =>
    Or.inr (hx.elim (fun hFirst => hFirst.symm ▸ first_inLine)
      (fun hSecond => hSecond.symm ▸ second_inLine))⟩

lemma base_ne_extras (x : Fin 13 → Bool) (h : atBase x) :
    x ≠ firstInput ∧ x ≠ secondInput :=
  ⟨fun hFirst => first_noBase (hFirst ▸ h), fun hSecond => second_noBase (hSecond ▸ h)⟩

def extras : Finset (Fin 13 → Bool) := {firstInput, secondInput}

lemma extras_card : extras.card = 2 := by simp [extras, first_ne_second]

lemma domain_filter :
    (Finset.univ.filter (fun x => atBase x ∨ inLine x)) = Finset.univ.filter atBase ∪ extras :=
  Finset.ext fun x => by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      extras, Finset.mem_insert, Finset.mem_singleton] using (domain_iff x)

lemma base_disjoint_extras : Disjoint (Finset.univ.filter atBase) extras :=
  Finset.disjoint_left.mpr fun {x} hx he =>
    have h := base_ne_extras x (Finset.mem_filter.mp hx).2
    have heq : x = firstInput ∨ x = secondInput := by simpa [extras] using he
    heq.elim h.1 h.2

lemma domain_card : (Finset.univ.filter (fun x => atBase x ∨ inLine x)).card = 7170 := by
  rw [domain_filter, Finset.card_union_of_disjoint base_disjoint_extras, base_card, extras_card]

lemma domain_upward (x y : Fin 13 → Bool) (hx : atBase x ∨ inLine x)
    (hxy : ∀ v : Fin 13, x v = true → y v = true) : atBase y ∨ inLine y :=
  hx.elim
    (fun ⟨v, hv, h⟩ => Or.inl ⟨v, hv, hxy v h⟩)
    (fun ⟨s, hs⟩ => Or.inr ⟨s, fun v h =>
      hs v (Bool.eq_false_of_not_eq_true (fun ht => Bool.false_ne_true (h.symm.trans (hxy v ht))))⟩)

end PEqualNP.Outside.L_meta_1520

open PEqualNP.Outside.L_meta_1520

theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  intro L hL
  have h : L = line := funext hL
  subst L
  exact ⟨domain_iff, base_ne_extras, domain_card, inLine_card, domain_upward⟩

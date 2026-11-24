import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- The search tests only the minimal true and maximal false assignments, and
-- checks the two finite traces for the fixed incident flag (0,0).
theorem PEqualNP.Outside.R_meta_1479_37
    (boundary : ∀ C : Circuit, AndOrOnly C →
      (∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
        C.eval (List.ofFn fun i : Fin 14 => decide (i = p.castAdd 7 ∨ i = l.natAdd 7)) = true) →
      (∀ j : Fin 37,
        C.eval (List.ofFn fun i : Fin 14 =>
          Nat.testBit ((((6652309773290916223743580559733800178712783036468204314834616147132044365135876578315935135840439337825392893246746424960835611371767624803298064203808640 : ℕ) >>> (14*j.val)) &&& 16383)) i.val) = false) →
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (p.castAdd 7) = true ∧ x (l.natAdd 7) = true)
    (search : ∃ (C : Circuit) (d : Bool → ℕ → Bool),
      C.size ≤ 27 ∧ IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
        C.eval (List.ofFn fun i : Fin 14 => decide (i = p.castAdd 7 ∨ i = l.natAdd 7)) = true) ∧
      (∀ j : Fin 37,
        C.eval (List.ofFn fun i : Fin 14 =>
          Nat.testBit ((((6652309773290916223743580559733800178712783036468204314834616147132044365135876578315935135840439337825392893246746424960835611371767624803298064203808640 : ℕ) >>> (14*j.val)) &&& 16383)) i.val) = false) ∧
      ∀ b : Bool,
        let seed : Fin 14 := if b then 7 else 0
        let base : Fin 14 := if b then 0 else 7
        let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = base))
        (∀ i : Fin 14, d b i.val = decide (i = seed)) ∧
        (∀ (j : ℕ) (g : Gate) (a c : ℕ), C.gates[j]? = some g → g.inputs = [a,c] →
          (g.op = .and → d b (14+j) = ((w.getD a false && d b c) || (d b a && w.getD c false))) ∧
          (g.op = .or → d b (14+j) = (d b a || d b c))) ∧ d b C.output = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨C, d, hSize, hAO, hDistinct, hPos, hNeg, hTrace⟩ := search
  refine ⟨C, hSize, ?_, boundary C hAO.1 hPos hNeg, 0, 0, Or.inl rfl, ?_, ?_⟩
  · intro j g hj
    have hjLen := (List.getElem?_eq_some_iff.mp hj).1
    have hMem := List.mem_of_getElem? hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 g hMem)
    have hg : gateAt C j = g := by
      change C.gates.getD j ⟨GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem?_getD, hj]
      rfl
    refine ⟨hAO.1 g hMem, a, b, hab, ?_, ?_, ?_⟩
    · simpa [hab] using hDistinct g hMem
    · apply hAO.2.1 j hjLen
      simp [hg, hab]
    · apply hAO.2.1 j hjLen
      simp [hg, hab]
  · obtain ⟨init, rule, out⟩ := hTrace true
    refine ⟨d true, ?_, rule, out⟩
    intro k
    have hp := init (k.castAdd 7)
    have hl := init (k.natAdd 7)
    have hn : (k.castAdd 7 : Fin 14) ≠ 7 := by
      intro he
      have h := congrArg Fin.val he
      simp at h
      omega
    change d true k.val = decide (k.castAdd 7 = (7 : Fin 14)) at hp
    change d true (7 + k.val) = decide (k.natAdd 7 = (7 : Fin 14)) at hl
    refine ⟨hp.trans (decide_eq_false hn), ?_⟩
    by_cases hk : k = 0
    · subst k
      exact hl
    · have hLine : (k.natAdd 7 : Fin 14) ≠ 7 := by
        intro h
        apply hk
        apply Fin.ext
        have eq := congrArg Fin.val h
        change 7 + k.val = 7 at eq
        change k.val = 0
        omega
      exact hl.trans (by rw [decide_eq_false hLine, decide_eq_false hk])
  · obtain ⟨init, rule, out⟩ := hTrace false
    refine ⟨d false, ?_, rule, out⟩
    intro k
    have hp := init (k.castAdd 7)
    have hl := init (k.natAdd 7)
    have hn : (k.natAdd 7 : Fin 14) ≠ 0 := by
      intro he
      have h := congrArg Fin.val he
      change 7 + k.val = 0 at h
      omega
    change d false k.val = decide (k.castAdd 7 = (0 : Fin 14)) at hp
    change d false (7 + k.val) = decide (k.natAdd 7 = (0 : Fin 14)) at hl
    refine ⟨?_, hl.trans (decide_eq_false hn)⟩
    by_cases hk : k = 0
    · subst k
      exact hp
    · have hPoint : (k.castAdd 7 : Fin 14) ≠ 0 :=
        fun h => hk (Fin.ext (congrArg (fun i : Fin 14 => i.val) h))
      exact hp.trans (by rw [decide_eq_false hPoint, decide_eq_false hk])

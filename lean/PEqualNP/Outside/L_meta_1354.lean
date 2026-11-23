import Mathlib.Data.List.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1354

-- A read beyond the final wire list returns false at every step.
private def moveWire (n sentinel i : ℕ) : ℕ :=
  if i < n then i else if i = n then sentinel else i - 1

private def moveGate (n sentinel : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (moveWire n sentinel)⟩

private def appendValue (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]

private theorem readWithFalse (front back : List Bool) (sentinel i : ℕ)
    (h : front.length + back.length ≤ sentinel) :
    (front ++ false :: back).getD i false =
      (front ++ back).getD (moveWire front.length sentinel i) false := by
  simp only [moveWire, List.getD_eq_getElem?_getD]
  by_cases hbefore : i < front.length
  · rw [ite_eq_left hbefore, List.getElem?_append_left hbefore, List.getElem?_append_left hbefore]
  · rw [ite_eq_right hbefore]
    by_cases hhere : i = front.length
    · rw [ite_eq_left hhere, List.getElem?_append_right (by omega),
        show i - front.length = 0 by omega, List.getElem?_cons_zero,
        List.getElem?_eq_none (l := front ++ back) (by simpa using h)]
      rfl
    · rw [ite_eq_right hhere, List.getElem?_append_right (l₁ := front) (l₂ := false :: back) (by omega),
        List.getElem?_append_right (l₁ := front) (l₂ := back) (by omega),
        show i - front.length = (i - 1 - front.length) + 1 by omega, List.getElem?_cons_succ]

private theorem evaluateWithFalse (front back : List Bool) (sentinel : ℕ) (gates : List Gate)
    (h : front.length + back.length + gates.length ≤ sentinel) :
    ∃ tail : List Bool,
      (gates.map (moveGate front.length sentinel)).foldl appendValue (front ++ back) =
        front ++ tail ∧
      gates.foldl appendValue (front ++ false :: back) = front ++ false :: tail := by
  induction gates generalizing back with
  | nil => exact ⟨back, rfl, rfl⟩
  | cons g rest ih =>
    have hargs :
        (moveGate front.length sentinel g).inputs.map (fun i => (front ++ back).getD i false) =
          g.inputs.map (fun i => (front ++ false :: back).getD i false) := by
      simp only [moveGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact (readWithFalse front back sentinel i (by omega)).symm
    let bit := g.op.eval (g.inputs.map fun i => (front ++ false :: back).getD i false)
    have hnext : front.length + (back ++ [bit]).length + rest.length ≤ sentinel := by
      simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega
    obtain ⟨tail, hleft, hright⟩ := ih (back ++ [bit]) hnext
    refine ⟨tail, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons]
      change List.foldl appendValue
        ((front ++ back) ++ [g.op.eval ((moveGate front.length sentinel g).inputs.map
          (fun i => (front ++ back).getD i false))]) _ = _
      rw [hargs]
      simpa only [List.append_assoc] using hleft
    · rw [List.foldl_cons]
      change List.foldl appendValue ((front ++ false :: back) ++ [bit]) rest = _
      simpa only [List.append_assoc, List.cons_append] using hright

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
      ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate,
        gates'.map PEqualNP.CircuitLowerBounds.Gate.op =
          gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧
        gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧
        ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length →
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) =
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  let sentinel := n + gates.length
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1354.moveGate n sentinel), ?_, ?_, ?_⟩
  · simp [List.map_map, PEqualNP.Outside.L_meta_1354.moveGate, Function.comp_def]
  · simp [List.map_map, PEqualNP.Outside.L_meta_1354.moveGate, Function.comp_def]
  · intro j x _
    let front := List.ofFn x
    have hfront : front.length = n := List.length_ofFn
    obtain ⟨tail, hnew, hold⟩ := PEqualNP.Outside.L_meta_1354.evaluateWithFalse front [] sentinel gates (by simp [hfront, sentinel])
    rw [hfront, List.append_nil] at hnew
    change ((gates.map (PEqualNP.Outside.L_meta_1354.moveGate n sentinel)).foldl PEqualNP.Outside.L_meta_1354.appendValue front).getD (n + j) false =
      (gates.foldl PEqualNP.Outside.L_meta_1354.appendValue (front ++ [false])).getD (n + 1 + j) false
    rw [hnew, hold]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (l₁ := front) (l₂ := tail) (by omega),
      List.getElem?_append_right (l₁ := front) (l₂ := false :: tail) (by omega),
      show n + j - front.length = j by omega, show n + 1 + j - front.length = j + 1 by omega,
      List.getElem?_cons_succ]

import PEqualNP.MetaComplexity.L011

namespace PEqualNP.Refutations.LMeta656

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two endpoints are inputs 0 and 1. Their disjunction can be shared.
private def passenger (x : Fin 3 → Bool) : Bool := (x 0 || x 1) && x 2

private def shortPath (x : Fin 4 → Bool) : Bool :=
  passenger (fun i => x i.castSucc) || (x 0 && x 3) || (x 3 && x 1)

private def leaf (a : Fin 4) (x : Fin 4 → Bool) : Bool :=
  passenger (fun i => x i.castSucc) || (x a && x 3)

private def separateLeaves (x : Fin 5 → Bool) : Bool :=
  passenger (fun i => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)

private def threeGates : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩], 6⟩

private theorem shortPath_upper : HasCircuitSize 4 shortPath 3 := by
  refine ⟨threeGates, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [threeGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide

private def UsesAll {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x

private theorem passenger_uses : UsesAll passenger := by
  unfold UsesAll
  decide

private theorem left_uses : UsesAll (leaf 0) := by
  unfold UsesAll
  decide

private theorem right_uses : UsesAll (leaf 1) := by
  unfold UsesAll
  decide

private theorem separate_uses : UsesAll separateLeaves := by
  unfold UsesAll
  decide

-- The first equivalence of the posted statement already fails at s = 3.
theorem refutation : ¬ (
    ∀ g : (Fin 3 → Bool) → Bool, (∀ x y : Fin 3 → Bool, (∀ i, x i = true → y i = true) → g x = true → g
    y = true) → g (fun _ : Fin 3 => false) = false → (∃ x : Fin 3 → Bool, g x = true) → (∃ x : Fin 3 →
    Bool, x 0 = true ∧ g x = false) → (∃ x : Fin 3 → Bool, x 1 = true ∧ g x = false) → ∀ s : ℕ,
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc)
    || (x 0 && x 3) || (x 3 && x 1)) s ↔ ((∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3
    g t) ∨ (∃ t : ℕ, 2 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g
    (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x
    : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨
    PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd
    2 i)) || (x 0 && x 3) || (x 1 && x 4)) s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin
    5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x
    1)) s ↔ ((∃ t : ℕ, 5 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 3 + t ≤ s ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc)
    || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i :
    Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 2 + t ≤ s ∧
    PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd
    2 i)) || (x 0 && x 3) || (x 1 && x 4)) t))) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin
    6 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 3 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5)
    || (x 5 && x 1)) s ↔ ((∃ t : ℕ, 6 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t :
    ℕ, 5 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3
    => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool
    => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 3 + t ≤ s ∧
    PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd
    2 i)) || (x 0 && x 3) || (x 1 && x 4)) t)))
    ) := by
  intro claim
  have mono : ∀ x y : Fin 3 → Bool, (∀ i, x i = true → y i = true) →
      passenger x = true → passenger y = true := by
    intro x y hxy hx
    simp only [passenger, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
    exact ⟨hx.1.imp (hxy 0) (hxy 1), hxy 2 hx.2⟩
  have someTrue : ∃ x, passenger x = true := ⟨fun _ => true, rfl⟩
  have endpoint₀ : ∃ x : Fin 3 → Bool, x 0 = true ∧ passenger x = false :=
    ⟨fun i => decide (i = 0), rfl, rfl⟩
  have endpoint₁ : ∃ x : Fin 3 → Bool, x 1 = true ∧ passenger x = false :=
    ⟨fun i => decide (i = 1), rfl, rfl⟩
  have alternatives := (claim passenger mono rfl someTrue endpoint₀ endpoint₁ 3).1.mp shortPath_upper
  -- The respective functions depend on 3, 4, 4 and 5 inputs.
  rcases alternatives with ⟨t, ht, h⟩ | ⟨t, ht, h | h⟩ | h
  · have := L011 3 passenger passenger_uses t h
    omega
  · have := L011 4 (leaf 0) left_uses t h
    omega
  · have := L011 4 (leaf 1) right_uses t h
    omega
  · have := L011 5 separateLeaves separate_uses 3 h
    omega

end PEqualNP.Refutations.LMeta656

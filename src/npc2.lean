import group_theory.subgroup.basic
import topology.metric_space.basic

noncomputable theory

variables {G : Type*} [group G] [decidable_eq G]

def word_norm {s : finset G}
  (h : subgroup.closure (s : set G) = ⊤) (h' : ∀ x ∈ s, x⁻¹ ∈ s) (g : G) : ℕ :=
Inf $ list.length '' { p : list G | p.prod = g ∧ (p.to_finset : set G) ⊆ s }

lemma subgroup.exists_list_prod_of_mem_closure {s : set G} {g : G}
  (h : g ∈ subgroup.closure s) (h' : ∀ x ∈ s, x⁻¹ ∈ s):
  ∃ (l : list G), l.prod = g ∧ (l.to_finset : set G) ⊆ s :=
begin
  refine subgroup.closure_induction h (λ x hx, _) _ _ _,
  { exact ⟨[x], by simp [hx]⟩, },
  { refine ⟨[], rfl, by simp⟩, },
  { rintros x y ⟨l, rfl, hl⟩ ⟨m, rfl, hm⟩,
    exact ⟨l ++ m, by simp [hl, hm]⟩, },
  { rintros - ⟨l, rfl, hl⟩,
    refine ⟨(l.map has_inv.inv).reverse, l.prod_inv_reverse.symm, λ x hx, _⟩,
    simp only [finset.mem_coe, list.to_finset_reverse, list.mem_to_finset, list.mem_map] at hx,
    obtain ⟨a, ha, rfl⟩ := hx,
    apply h' a (hl _),
    simpa, },
end

lemma word_norm_ne_zero {s : finset G}
  (h : subgroup.closure (s : set G) = ⊤) (h' : ∀ x ∈ s, x⁻¹ ∈ s) (g : G) :
  word_norm h h' g ≠ 0 :=
begin
  let X := { p : list G | p.prod = g ∧ (p.to_finset : set G) ⊆ s },
  have hX : X.nonempty,
  { change ∃ p : list G, p.prod = g ∧ (p.to_finset : set G) ⊆ s,
    have hg : g ∈ subgroup.closure (s : set G), { simp [h], },
    exact subgroup.exists_list_prod_of_mem_closure hg h', },
  -- etc.
  sorry,
end

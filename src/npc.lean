import topology.metric_space.basic
import algebra.group.basic
import data.list
-- instance : has_dist ℕ := ⟨λ x y, dist (x : ℝ) y⟩


-- (S : finset G), S.card = n ∧ subgroup.closure ↑S = ⊤)

-- instance word_metric {G : Type*} [group G] (S : finset G) : has_dist

-- def word_metric {G : Type*} [group G] (S : finset G) 

variables {G : Type*} [group G]

-- use "finite s" instead?
noncomputable def word_norm (s : finset G) (h : subgroup.closure (s : set G) = ⊤) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) (g : G) : ℕ :=
begin
  classical,
  let X : set (list G) := { p | list.prod p = g ∧ p.to_finset ⊆ s },
  have hX : X.nonempty, { 
    have hg : g ∈ subgroup.closure (s : set G), {
      simp [h],
    },
    suffices : ∃ (p : list G), list.prod p = g ∧ p.to_finset ⊆ s ), {
      obtain ⟨ p , hp ⟩ := this,
      use p,   
      exact hp,
    },
    apply subgroup.closure_induction hg, {
      intros x hx,
      use ([x] : list G),
      simpa using hx,
    },
    {
      use ([] : list G),
      simp,
    },
    {
      rintros x y ⟨ px, hx1, hx2 ⟩ ⟨ py, hy1, hy2 ⟩,
      use px ++ py,
      simp [hx1,hy1],
      exact finset.union_subset hx2 hy2,
    },
    {
      rintros x ⟨ p , hp1, hp2 ⟩,
      use (p.map (λ g , g⁻¹)).reverse,
      simp [hp1,hp2],
      split, {
        rw ← hp1,
        rw list.prod_inv_reverse,
      }, {
        intros x hx,
        simp at hx,
        obtain ⟨ a, ha, hai ⟩ := hx,
        specialize hinv a,
        rw ← hai,
        apply hinv,
        apply hp2,
        simpa,
      },
    },
  },
  exact Inf ( list.length '' X ),
end

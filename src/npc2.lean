import group_theory.subgroup.basic
import topology.metric_space.basic
import data.list.basic
import data.set
import data.finset
import data.real.ennreal

noncomputable theory

variables {G : Type*} [group G] [decidable_eq G]

-- inv_mem_class S G
--class generated_group (gens : set G) extends group G :=
--   (inv_mem' : ∀ x ∈ gens, x⁻¹ ∈ gens) 

/-- `subfield_class S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
--class subfield_class (S : Type*) (K : out_param $ Type*) [field K] [set_like S K]
--  extends subring_class S K, inv_mem_class S K.

--class generator_class (S G : Type*) [group G] [set_like S G] :=
--  (generates : subgroup.closure S.to_set = ⊤)

--def generated_group_coe_subgroup (gens : set G) [generated_group gens] : subgroup G :=
--  subgroup.closure gens

def word_enorm (s : set G) (g : G) : ennreal :=
  let length (x : list G) : ennreal := list.length x in
  Inf $ length '' { p : list G | p.prod = g ∧ (p.to_finset : set G) ⊆ s }

def word_edist (s : set G) (x y : G) := word_enorm s (x * y⁻¹)

def word_edist_self (s : set G) (g : G) : (word_edist s) g g = 0 :=
begin
end


def word_eq_of_edist_eq_zero (s : set G) : ∀ (x y : G), (word_edist s) x y = 0 → x = y :=
begin
  sorry
end

def word_edist_comm (s : set G) : ∀ (x y : G), (word_edist s) x y = (word_edist s) y x :=
begin
  sorry
end

def word_edist_triangle (s : set G) : ∀ (x y z : G), (word_edist s) x z ≤ (word_edist s) x y + (word_edist s) y z :=
begin
  sorry
end

def word_emetric_space (s : set G) : emetric_space G :=
{ edist := word_edist s,
  edist_self := word_edist_self s,
  eq_of_edist_eq_zero := word_eq_of_edist_eq_zero s,
  edist_comm := word_edist_comm s,
  edist_triangle := word_edist_triangle s
}

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
  word_norm g ≠ 0 :=
begin
  let X := { p : list G | p.prod = g ∧ (p.to_finset : set G) ⊆ s },
  have hX : X.nonempty,
  { change ∃ p : list G, p.prod = g ∧ (p.to_finset : set G) ⊆ s,
    have hg : g ∈ subgroup.closure (s : set G), { simp [h], },
    exact subgroup.exists_list_prod_of_mem_closure hg h', },
  -- etc.
  sorry,
end

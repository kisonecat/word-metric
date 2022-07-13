import group_theory.subgroup.basic
import topology.metric_space.basic
import data.list.basic
import data.finset
import data.set
import data.real.ennreal
import order.complete_lattice
import order.bounded_order

noncomputable theory

@[derive [
  has_zero, add_comm_monoid_with_one,
  canonically_ordered_comm_semiring, complete_linear_order, nontrivial,
  canonically_linear_ordered_add_monoid, has_sub, has_ordered_sub,
  linear_ordered_add_comm_monoid_with_top]]
def enat' := with_top nat

def to_ennreal : enat' → ennreal 
| (some n) := (n : ennreal)
| none := (none : ennreal)

lemma lt_wf : @well_founded enat' (<) :=
begin
  apply with_top.well_founded_lt,
  exact nat.lt_wf,
end

instance : has_well_founded enat' := ⟨(<), lt_wf⟩
instance enat'.lt.is_well_order : is_well_order enat' (<) := ⟨lt_wf⟩

variables {G : Type*} [group G] [decidable_eq G] 

variables (s : set G)

def length (x : list G) : enat' := list.length x

def words (x : G) : (set (list G)) := { p : list G | p.prod = x ∧ (p.to_finset : set G) ⊆ s }

def word_enorm (g : G) : enat' := Inf $ length '' (words s g)
 
lemma enorm_one_is_zero : word_enorm s (1 : G) = 0 :=
begin
  have k : word_enorm s 1 ≤ 0,
  { 
    unfold word_enorm,
    have k : 0 ∈ length '' { p : list G | p.prod = 1 ∧ (p.to_finset : set G) ⊆ s },
    simp,
    use ([] : list G),
    simp,
    unfold length,
    simp,
    exact Inf_le k,
  },
  finish,
end

lemma enat_Inf_mem_zero (s : set enat') (h : Inf s = 0) : (0 : enat') ∈ s :=
begin
  cases s.eq_empty_or_nonempty with k k,
  {
    exfalso,
    rw k at h,
    rw Inf_empty at h,
    exact with_top.top_ne_coe h,
  },
  {
    have hi := Inf_mem k,
    rwa h at hi,
  },
end

lemma enorm_eq_zero (g : G) : word_enorm s g = 0 → g = 1 :=
begin
  intro h,
  have k : 0 ∈ length '' { p : list G | p.prod = g ∧ (p.to_finset : set G) ⊆ s },
  apply enat_Inf_mem_zero,
  assumption,
  simp at k,
  obtain ⟨ x, ⟨ h1, h2 ⟩, h3 ⟩ := k,
  unfold length at h3,
  simp at h3,
  rw list.length_eq_zero at h3,
  rw h3 at h1,
  simp at h1,
  exact h1.symm,
end

lemma enorm_zero_iff_one (g : G) : word_enorm s g = 0 ↔ g = 1 :=
begin
  split,
  { 
    intro h,
    -- why does this introduce m_1?
    apply enorm_eq_zero,
    assumption, 
  },
  {
    intro h,
    rw h,
    rw enorm_one_is_zero,
  },
end

lemma word_enorm_ineq (inv_mem : ∀ x ∈ s, x⁻¹ ∈ s) (x : G) : word_enorm s x⁻¹ ≤ word_enorm s x :=
begin
  have ws := words s x,
  have wi := words s x⁻¹,
  
  have k : (length '' words s x) ⊆ (length '' words s x⁻¹),
  {
    intros lp h,
    simp at h, 
    obtain ⟨ p , hp, hl ⟩ := h,
    cases hp with hp1 hp2,
    simp,
   
    use (list.map (λ (x : G), x⁻¹) p).reverse,
    unfold words,
    simp,
    rw ← p.prod_inv_reverse,
    rw hp1,
    split, split,
    { refl, },

    { 
      intro g,
      simp,
      intros x hxp hxg,
      rw ← hxg,
      apply inv_mem,
      apply hp2,
      simp,
      apply hxp,
    },
 
    {
      rw ← hl,
      unfold length at *,
      simp,
    },
  },
  
  unfold word_enorm at *,
  exact Inf_le_Inf k, 
end

lemma word_enorm_eq (inv_mem : ∀ x ∈ s, x⁻¹ ∈ s) (x : G) : word_enorm s x = word_enorm s x⁻¹ :=
begin
  have lt : word_enorm s x⁻¹ ≤ word_enorm s x := word_enorm_ineq s inv_mem x,
  apply le_antisymm,
  { 
    have h : word_enorm s x⁻¹⁻¹ ≤ word_enorm s x⁻¹ := word_enorm_ineq s inv_mem x⁻¹,
    simp at h,
    assumption,
  },
  { assumption, },
end

def word_edist (x y : G) : enat' := word_enorm s (x * y⁻¹)

def edist_to_enorm {x y : G} : word_edist s x y = word_enorm s (x * y⁻¹) := by refl

def word_edist_self (g : G) : word_edist s g g = 0 :=
begin
  rw edist_to_enorm s,
  simp,
  exact enorm_one_is_zero s,
end

def word_eq_of_edist_eq_zero : ∀ (x y : G), (word_edist s) x y = 0 → x = y :=
begin
  intros x y,
  intro h,
  rw edist_to_enorm at h,
  have k := enorm_eq_zero s _ h, 
  group at k ⊢,
  assumption,
end

def word_edist_comm (inv_mem : ∀ x ∈ s, x⁻¹ ∈ s) (x y : G) : (word_edist s) x y = (word_edist s) y x :=
begin
  unfold word_edist,
  rw word_enorm_eq s,
  simp,
  exact inv_mem,
end

def words_empty_enorm_top (x : G) (h : words s x = ∅) : word_enorm s x = ⊤ :=
begin
  unfold word_enorm,
  rw h,
  simp, 
end

def word_enorm_triangle (x y : G) : word_enorm s (x * y) ≤ word_enorm s x + word_enorm s y :=
begin
  cases (words s x).eq_empty_or_nonempty with wxe wxn,
  { rw words_empty_enorm_top s x wxe, simp, },
  {
    cases (words s y).eq_empty_or_nonempty with wye wyn,
    { rw words_empty_enorm_top s y wye, simp, },
    { 
      obtain ⟨ px, ⟨ hPx, hsx ⟩, hlx ⟩ := Inf_mem (set.nonempty.image length wxn),
      obtain ⟨ py, ⟨ hPy, hsy ⟩, hly ⟩ := Inf_mem (set.nonempty.image length wyn),

      have h : px ++ py ∈ words s (x * y) := begin
        unfold words,
        simp,
        split,
        {
          rw [hPx, hPy], 
        },
        {
          exact ⟨ hsx, hsy ⟩,   
        },
      end,

      cases (words s (x * y)).eq_empty_or_nonempty with wxye wxyn, 
      {
        exfalso,
        finish,
      },
      {
        unfold word_enorm,
        rw [←hlx, ←hly],
        
        have k : Inf (length '' words s (x * y)) ≤ length (px ++ py) := cInf_le' (set.mem_image_of_mem length h), 
        have k2 : length (px ++ py) = length px + length py := begin
          unfold length,
          simp,
        end,

        rwa ← k2,
      },
    },
  },
end

def word_edist_triangle : ∀ (x y z : G), (word_edist s) x z ≤ (word_edist s) x y + (word_edist s) y z :=
begin
  unfold word_edist,
  intros x y z,
  have hxz : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group,
  rw hxz,
  apply word_enorm_triangle s,
end

-- trouble with ennreal versus enat'
def word_emetric_space (inv_mem : ∀ x ∈ s, x⁻¹ ∈ s) : emetric_space G :=
{ edist := word_edist s,
  edist_self := word_edist_self,
  eq_of_edist_eq_zero := word_eq_of_edist_eq_zero,
  edist_comm := word_edist_comm,
  edist_triangle := word_edist_triangle
}

-- the additional hypothesis here will produce a METRIC space
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

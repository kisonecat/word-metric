import group_theory.subgroup.basic
import group_theory.free_group
import data.set.basic
import algebra.hom.group

import topology.metric_space.basic
import data.list.basic
import data.finset
import data.set
import data.real.ennreal
import order.complete_lattice
import order.bounded_order

noncomputable theory

variables {G : Type*} [group G] [decidable_eq G] 

@[class]
structure generated_group (G : Type*) [group G] :=
  (gens : set G)
  (closure_eq_top : subgroup.closure gens = ⊤) 

instance {α : Type*} : generated_group (free_group α) := 
{ gens := set.range free_group.of, 
  closure_eq_top := by begin
    rw [← free_group.lift.range_eq_closure, monoid_hom.range_top_iff_surjective ],
    intro x, use x,
    exact free_group.lift.of_eq x,
  end
}

variables (GG : generated_group G)

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
def of (x : free_group GG.gens) : G := begin
  refine free_group.lift _ x,
  intro g,
  use g,
end

def words (g : G) : set (free_group GG.gens) := { w : free_group GG.gens | of GG w = g }

def word_norm (g : G) : nat := Inf $ list.length '' (free_group.to_word '' (words GG g))

lemma norm_one_eq_zero : word_norm GG (1 : G) = 0 :=
begin
  set ws := words GG 1 with hws,
  
  suffices : 0 ∈ list.length '' (free_group.to_word '' ws),
  { 
    rw [← nonpos_iff_eq_zero],
    refine nat.Inf_le this , 
  },
  refine ⟨ [], _ ⟩, 
  simp only [list.length, set.mem_image, eq_self_iff_true, and_true],
  use 1,

  have h2 : (1 : free_group GG.gens) ∈ ws,
  { rw hws,
    simp [of, words], },
  refine ⟨ h2, _ ⟩,

  change (free_group.mk list.nil).to_word = list.nil,
  rw ← free_group.red.nil_iff,
  unfold free_group.to_word,
  
  simp only [free_group.quot_lift_mk],
  rw free_group.red.nil_iff ,
  unfold free_group.reduce,
end

lemma norm_eq_zero (g : G) : word_norm GG g = 0 → g = 1 :=
begin
  sorry
end

@[simp] lemma norm_zero_iff_one (g : G) : word_norm GG g = 0 ↔ g = 1 :=
begin
  sorry
end

lemma word_norm_le_inv (x : G) : word_norm GG x⁻¹ ≤ word_norm GG x :=
begin
  sorry
end

lemma word_norm_symm (x : G) : word_norm GG x = word_norm GG x⁻¹ :=
begin
  sorry
end

def word_dist (x y : G) : nat := word_norm GG (x * y⁻¹)

def dist_to_norm {x y : G} : word_dist GG x y = word_norm GG (x * y⁻¹) := by refl

def word_dist_self (g : G) : word_dist GG g g = 0 :=
begin
  rw dist_to_norm s,
  simp,
  exact norm_one_eq_zero s,
end

def word_eq_of_edist_eq_zero : ∀ (x y : G), word_dist GG x y = 0 → x = y :=
begin
  intros x y,
  intro h,
  rw dist_to_norm at h,
  have k := norm_eq_zero GG _ h, 
  group at k ⊢,
  assumption,
end

def word_dist_comm (x y : G) : word_dist GG x y = word_dist GG y x :=
begin
  unfold word_dist,
  rw word_norm_symm GG,
  simp,
end

def word_norm_triangle (x y : G) : word_norm GG (x * y) ≤ word_norm GG x + word_norm GG y :=
begin
  sorry
end

def word_dist_triangle : ∀ (x y z : G), word_dist GG x z ≤ word_dist GG x y + word_dist GG y z :=
begin
  unfold word_dist,
  intros x y z,
  have hxz : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group,
  rw hxz,
  apply word_norm_triangle GG,
end

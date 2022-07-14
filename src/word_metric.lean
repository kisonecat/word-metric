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

def words_nonempty (g : G) : (words GG g).nonempty := begin
  have h : ∃ w : free_group GG.gens, w ∈ words GG g, {
    let hk := GG.closure_eq_top,

    let f := free_group.lift (id : GG.gens → GG.gens),

    rw [← free_group.lift.range_eq_closure, monoid_hom.range_top_iff_surjective ],
    intro x, use x,
    exact free_group.lift.of_eq x,
    
    sorry,
  },
  exact h,
end  

-- should be in terms of has_norm
def word_norm (g : G) : nat := Inf $ (list.length ∘ free_group.to_word) '' (words GG g)

-- this is surely much too long
lemma norm_one_eq_zero : word_norm GG (1 : G) = 0 :=
begin
  set ws := words GG 1 with hws,
  
  suffices : 0 ∈ (list.length ∘ free_group.to_word) '' ws,
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
  intro h,
   
  let lw := (list.length ∘ free_group.to_word) '' (words GG g),
  have hl : set.nonempty lw := begin
    simp only [set.nonempty_image_iff],
    exact words_nonempty GG g,
  end,
  
  have hk := nat.Inf_mem hl,
  unfold word_norm at h,
  rw h at hk,
  simp only [set.mem_image, exists_exists_and_eq_and] at hk,
  obtain ⟨ w, h2, h3 ⟩ := hk,
  unfold words at h2,
  simp only [set.mem_set_of_eq] at h2,
  rw list.length_eq_zero at h3,

  have h4 : (1 : free_group GG.gens).to_word = list.nil, {
    unfold free_group.to_word,
    unfold has_one.one,
    rw ← free_group.red.nil_iff,
    simp only [free_group.quot_lift_mk],
    rw free_group.red.nil_iff ,
    unfold free_group.reduce,
  },
  
  rw ← h3 at h4,

  have h5 : w = 1, {
    apply free_group.to_word.inj,
    assumption,
  },

  rw h5 at h2,

  unfold of at h2,  
  simp only [map_one] at h2,
  exact h2.symm, 
end

@[simp] lemma norm_zero_iff_one (g : G) : word_norm GG g = 0 ↔ g = 1 :=
begin
  refine ⟨ norm_eq_zero GG g, _ ⟩,
  rintro rfl,
  apply norm_one_eq_zero,
end

theorem nat.Inf_le_Inf {s t : set ℕ} (hs : s.nonempty) (ht : s ⊆ t) : Inf t ≤ Inf s 
:= nat.Inf_le $ ht $ nat.Inf_mem hs

lemma word_norm_le_inv (x : G) : word_norm GG x⁻¹ ≤ word_norm GG x :=
begin
  set ws := words GG x with hws,
  set wi := words GG x⁻¹ with hwi,
  
  let lw := (list.length ∘ free_group.to_word) '' ws,
  have k : lw ⊆ (list.length ∘ free_group.to_word) '' wi),
  {
    intros lp h,
    simp only [set.mem_image, exists_exists_and_eq_and] at h,
    obtain ⟨ p , hp, hl ⟩ := h,
    simp,
  
    use p⁻¹,

    split,
    { 
       rw hws at hp,
       unfold words at hp,
       simp at hp,
       unfold of at hp,
       
       rw hwi,
       unfold words,
       simp only [set.mem_set_of_eq],
       unfold of,

       simp only [map_inv, inv_inj] at hp ⊢,
       assumption,
    }, 
    {
      rw ← hl,
      simp,
      sorry,
    },
  },
  unfold word_norm at *,

  have hl : set.nonempty lw := begin
    simp only [set.nonempty_image_iff],
    exact words_nonempty GG x,
  end,
  
  exact nat.Inf_le_Inf hl k, 
end

lemma word_norm_symm (x : G) : word_norm GG x = word_norm GG x⁻¹ :=
begin
  have lt : word_norm GG x⁻¹ ≤ word_norm GG x := word_norm_le_inv GG x,
  apply le_antisymm,
  { 
    have h : word_norm GG x⁻¹⁻¹ ≤ word_norm GG x⁻¹ := word_norm_le_inv GG x⁻¹,
    simp at h,
    assumption,
  },
  { assumption, },
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
  set wx := words GG x with hwx,
  set wy := words GG y with hwy,
  set wxy := words GG (x * y) with hwxy,

  let lx := (list.length ∘ free_group.to_word) '' wx,
  have hlx : set.nonempty lx := begin
    simp only [set.nonempty_image_iff],
    exact words_nonempty GG x,
  end,

  let ly := (list.length ∘ free_group.to_word) '' wy,
  have hly : set.nonempty ly := begin
    simp only [set.nonempty_image_iff],
    exact words_nonempty GG y,
  end,

  rcases nat.Inf_mem hlx with ⟨ px, hx2, hx3 ⟩,
  rcases nat.Inf_mem hly with ⟨ py, hy2, hy3 ⟩,

  have h : px * py ∈ words GG (x * y) := begin
    sorry,
  end,

  unfold word_norm,
  rw [←hx3, ←hy3],
        
  have k : Inf ((list.length ∘ free_group.to_word) '' (words GG (x * y))) ≤ (list.length ∘ free_group.to_word) (px * py) := begin
    sorry,
  end, 
  have k2 : (list.length ∘ free_group.to_word) (px * py) ≤ (list.length ∘ free_group.to_word) px + (list.length ∘ free_group.to_word) py := begin
    simp,
    sorry, 
  end,
  finish,
end

def word_dist_triangle : ∀ (x y z : G), word_dist GG x z ≤ word_dist GG x y + word_dist GG y z :=
begin
  unfold word_dist,
  intros x y z,
  have hxz : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group,
  rw hxz,
  apply word_norm_triangle GG,
end

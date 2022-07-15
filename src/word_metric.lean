import group_theory.subgroup.basic
import analysis.normed.group.basic
import topology.metric_space.basic

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

import fg_norm

noncomputable theory

theorem nat.Inf_le_Inf {s t : set ℕ} (hs : s.nonempty) (ht : s ⊆ t) : Inf t ≤ Inf s 
:= nat.Inf_le $ ht $ nat.Inf_mem hs

@[class]
structure generated_group (G : Type*) extends group G :=
(gens : set G)
(closure_eq_top : subgroup.closure gens = ⊤) 

variables {G : Type*} [generated_group G] [decidable_eq G] 

namespace generated_group

open generated_group

def of (x : free_group (gens : set G)) : G := begin
  refine free_group.lift _ x,
  intro g,
  use g,
end

def of_mul (x : free_group (gens : set G)) (y : free_group (gens : set G)) : of (x * y) = of x * of y :=
begin
  unfold of,
  simp,
end

def words (x : G) : set (free_group (gens : set G)) := of ⁻¹' { x }

def words_of {x : G} {w : free_group (gens : set G)} (h : w ∈ words x) : of w = x :=
begin
  unfold words at h,
  simp only [set.mem_preimage, set.mem_singleton_iff] at h,
  exact h, 
end

def words_inv (x : G) : (words x) = has_inv.inv '' (words x⁻¹) :=
begin
  unfold words,
  ext,
  split, 
  {
    simp only [set.mem_preimage, set.mem_singleton_iff, set.image_inv, set.mem_inv],
    intro h,
    rw ← h,
    simp only [map_inv, of],
  },
  {
    simp only [set.image_inv, set.mem_inv, set.mem_preimage, set.mem_singleton_iff],
    intro h,
    have hk : (of x_1⁻¹)⁻¹ = x,
    { exact inv_eq_iff_inv_eq.mp (eq.symm h) },
    rw ← hk,
    simp [of],
  },
end

def push_inv (x : G) : (words x⁻¹) = has_inv.inv '' (words x) :=
begin
  have k := words_inv x⁻¹,
  finish,
end

def words_nonempty (x : G) : (words x).nonempty :=
begin
  have hk := @closure_eq_top G _,
  unfold words,
  unfold set.nonempty,
  simp only [set.mem_preimage, set.mem_singleton_iff],

  set f : (gens → G) := (λ a : (gens : set G), a) with hf,

  have hr : set.range f = (gens : set G),
  {
    ext,
    split,
    { finish, },
    { intro h,
      use x_1,
      use h,
      finish, },
  },  

  have h : _ = subgroup.closure (set.range f) := free_group.lift.range_eq_closure  ,

  rw hr at h,
  rw hk at h,

  rw monoid_hom.range_top_iff_surjective at h,
 
  unfold of,

  rw ← hf ,

  exact h x,
end

def nat_norm (x : G) : nat := Inf $ free_group.nat_norm '' (words x)

def norm (x : G) : ℝ := nat_norm x

instance : has_norm G := ⟨norm⟩

def dist (x : G) (y : G) : ℝ := ∥ x * y⁻¹ ∥

instance : has_dist G := ⟨dist⟩

def norm_eq (x : G) : ∥ x ∥ = nat_norm x := rfl

def norm_inv_le (x : G) : ∥ x⁻¹ ∥ ≤ ∥ x ∥ :=
begin
  rw norm_eq, rw norm_eq,
  norm_cast,

  rw nat_norm, rw nat_norm,
  apply nat.Inf_le_Inf,
  {
    have hne := words_nonempty x,
    exact set.nonempty.image free_group.nat_norm hne,
  },
  {  
    rw push_inv,
    intros nw hnw,
    simp only [set.mem_image] at hnw,
    simp only [set.image_inv, set.mem_image, set.mem_inv],
    cases hnw with fw hfw,
    use fw⁻¹,
    simp,
    refine ⟨ hfw.1, _ ⟩,
    rw ← hfw.2,
    symmetry,
    have k := free_group.norm_inv fw,
    rw free_group.norm_eq at k,
    rw free_group.norm_eq at k,
    norm_cast at k,
    assumption,
  },
end

def norm_inv (x : G) : ∥ x ∥ = ∥ x⁻¹ ∥ :=
begin
  have h := norm_inv_le x,
  have hi := norm_inv_le x⁻¹,
  simp at hi,
  finish,
end

def dist_eq (x y : G) : dist x y = nat_norm (x * y⁻¹) := rfl

def dist_self (x : G) : dist x x = 0 :=
begin
  rw dist_eq,
  norm_cast,
  
  rw nat_norm,

  suffices : Inf (free_group.nat_norm '' words (x * x⁻¹)) ≤ 0,
  { exact le_zero_iff.mp this, },

  suffices : 0 ∈ free_group.nat_norm '' words (x * x⁻¹),
  { apply nat.Inf_le this, },

  simp only [mul_right_inv, set.mem_image],
  use 1,

  split,
  { simp only [words, of], },
  { unfold free_group.nat_norm,
    rw list.length_eq_zero,
    exact free_group.one_to_word, 
  }, 
end

def dist_comm (x y : G) : dist x y = dist y x :=
begin
  rw dist_eq, rw dist_eq,
  norm_cast,

  set z := x * y⁻¹,
  set zi := y * x⁻¹,

  have h : zi = z⁻¹,
  { simp only [mul_inv_rev, inv_inv], },

  have hk := norm_inv z,
  rw norm_eq at hk,
  rw norm_eq at hk,
  norm_cast at hk,
  rwa h,
end

def dist_triangle (x y z : G) : (dist x z) ≤ (dist x y) + (dist y z) :=
begin
  rw dist_eq,
  rw dist_eq,
  rw dist_eq,
  norm_cast,
 
  set xz := x * z⁻¹ with hxz,
  set xy := x * y⁻¹ with hxy,
  set yz := y * z⁻¹ with hyz,

  unfold nat_norm,

  have h1 := nat.Inf_mem (by simp [words_nonempty] : (free_group.nat_norm '' words xy).nonempty),
  have h2 := nat.Inf_mem (by simp [words_nonempty] : (free_group.nat_norm '' words yz).nonempty),

  cases h1 with wxy hwxy,
  cases h2 with wyz hwyz,
      
  rw ← hwyz.2,
  rw ← hwxy.2,

  have h : wxy * wyz ∈ words xz,
  {
    unfold words,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    rw of_mul,
    have hxyw := words_of hwxy.1,
    have hyzw := words_of hwyz.1,
    rw hxyw,
    rw hyzw,
    rw hxy,
    rw hyz,
    rw hxz,
    group,
  },

  have h2 : free_group.nat_norm (wxy * wyz) ∈ free_group.nat_norm '' (words xz), 
  { exact set.mem_image_of_mem free_group.nat_norm h, },

  have h3 : Inf ( free_group.nat_norm '' words xz ) ≤ free_group.nat_norm (wxy * wyz ),
  {
    exact cInf_le' h2,
  },
   
  have h4 : free_group.nat_norm( wxy * wyz ) ≤ wxy.nat_norm + wyz.nat_norm,
  {
     have h5 : ∥ wxy * wyz ∥ ≤ ∥ wxy ∥ + ∥ wyz ∥ := free_group.norm_triangle _ _,
     rw free_group.norm_eq at h5,
     rw free_group.norm_eq at h5,
     rw free_group.norm_eq at h5,
     norm_cast at h5,
     assumption, 
  }, 
  
  finish,
end

def eq_of_dist_eq_zero (x y : G) : dist x y = 0 → x = y := 
begin
  rw dist_eq,
  intro h,
  norm_cast at h,

  unfold nat_norm at h,

  rw nat.Inf_eq_zero at h,
  cases h,
  { simp only [set.mem_image] at h,
    rcases h with ⟨ w, hw1, hw2 ⟩,
    have hk := free_group.norm_zero_eq_one w,
    have hi : w = 1, { apply hk, rw free_group.norm_eq, norm_cast, assumption, },
  
    rw hi at hw1,
  
    unfold words at hw1,
    simp [of] at hw1,
    group, -- this should be simpler?
    rw hw1,
    group, 
  },
  {
    exfalso, 
    have hne := words_nonempty (x * y⁻¹),
    finish,
  },
end

instance : pseudo_metric_space G :=
{ dist               := dist,
  dist_self          := dist_self,
  dist_comm          := dist_comm,
  dist_triangle      := dist_triangle }

instance : metric_space G :=
{ eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end generated_group


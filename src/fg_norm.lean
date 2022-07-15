import group_theory.free_group
import group_theory.subgroup.basic
import analysis.normed.group.basic

namespace free_group

variables {α : Type*} [decidable_eq α]

def one_to_word : (1 : free_group α).to_word = list.nil := begin
  rw one_eq_mk,
  unfold to_word,
  simp only [quot_lift_mk],
  rw ← free_group.red.nil_iff ,
  simp only [reduce.red],
end

def nat_norm (x : free_group α) : nat := x.to_word.length

def norm (x : free_group α) : ℝ := nat_norm x

instance : has_norm (free_group α) := ⟨norm⟩

def norm_eq (x : free_group α) : ∥ x ∥ = nat_norm x := rfl

def reduced_is_shorter {L₁ : list (α × bool)} {L₂ : list (α × bool)} (h : free_group.red L₁ L₂) : (L₁.length ≥ L₂.length) :=
begin
  induction h with h1 h2 h3 h4,
  { exact rfl.ge, },
  { let hk := h4.length,
    linarith, },
end

def reduced_is_shortest (x : free_group α) (w : list (α × bool)) (h : free_group.mk w = x) : x.to_word.length ≤ w.length := 
begin
  suffices k : red w (x.to_word),
  { apply reduced_is_shorter,
    assumption,
  },
  
  rw ← h,
  unfold to_word, 
  simp [reduce.red],
end

def inv_rev (w : list (α × bool)) : list (α × bool) :=
 (list.map (λ (g : α × bool), (g.fst, !g.snd)) w).reverse 

def inv_rev_eq {w : list (α × bool)} :=
 inv_rev w = (list.map (λ (g : α × bool), (g.fst, !g.snd)) w).reverse 

def inv_rev_length { w : list ( α × bool ) } : (inv_rev w).length = w.length:=
begin
  induction w,
  { finish, },
  unfold inv_rev,
  { finish, },
end

def inv_rev_involutive { w : list ( α × bool ) } : (inv_rev (inv_rev w) = w) :=
begin
 induction w,
 { finish, },
 unfold inv_rev,
 rw list.map_reverse,
 rw list.map_map,
 simp only [list.map, function.comp_app, bnot_bnot, prod.mk.eta, list.reverse_reverse, eq_self_iff_true, true_and],
 have h : ((λ (g : α × bool), (g.fst, !g.snd)) ∘ (λ (g : α × bool), (g.fst, !g.snd))) = id,
 { funext, simp, },

 rw h,
 simp, 
end

def inv_to_word_le (x : free_group α) : (x⁻¹).to_word.length ≤ x.to_word.length :=
begin
  set w := x.to_word with hw,
 
  have k7 : (mk w)⁻¹ = mk (inv_rev w) := inv_mk, 
  have k9 : mk (inv_rev w) = x⁻¹, 
  { 
    nth_rewrite 0 hw at k7,
    rw to_word.mk at k7,
    exact k7.symm,
  },

  have k8 : (x⁻¹).to_word.length ≤ (inv_rev w).length := reduced_is_shortest (x⁻¹) (inv_rev w) k9,

  rw inv_rev_length at k8,
  assumption, 
end

def norm_inv_le (x : free_group α) : ∥ x⁻¹ ∥ ≤ ∥ x ∥ :=
begin
  rw norm_eq,
  rw norm_eq,
  norm_cast,
  unfold nat_norm,
  exact inv_to_word_le x,  
end

def norm_inv (x : free_group α) : ∥ x ∥ = ∥ x⁻¹ ∥ :=
begin
  have h1 := norm_inv_le x,
  have h2 := norm_inv_le x⁻¹,
  simp at h2,
  finish,
end

def norm_zero_eq_one (x : free_group α ) : ∥ x ∥ = 0 → x = 1 := 
begin
  intro h,
  rw norm_eq at h,
  norm_cast at h,
  unfold nat_norm at h,
  rw list.length_eq_zero at h,
  rw ← one_to_word at h,
  exact to_word.inj x 1 h,
end

def norm_triangle (x : free_group α) (y : free_group α) : ∥ x * y ∥ ≤ ∥ x ∥ + ∥ y ∥ :=
begin
  rw norm_eq, rw norm_eq, rw norm_eq,
  norm_cast,
  unfold free_group.nat_norm,
  
  set wx := x.to_word with hwx,
  set wy := y.to_word with hwy,

  set wxy := wx ++ wy with hwxy,
  rw ←list.length_append,
   
  apply reduced_is_shortest,
  rw [← mul_mk, to_word.mk, to_word.mk ],
end

end free_group

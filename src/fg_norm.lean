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
  sorry,
end

def inv_rev_involutive { w : list ( α × bool ) } : (inv_rev (inv_rev w) = w) :=
begin
 induction w,
 { finish, },
 unfold inv_rev,
 rw list.map_reverse,
 rw list.map_map,
 simp,
 have h : ((λ (g : α × bool), (g.fst, !g.snd)) ∘ (λ (g : α × bool), (g.fst, !g.snd))) = id,
 { ext; simp, },

 rw h,
 simp, 
end

def inv_rev_cons {hd : α × bool} {tl : list (α × bool)} : inv_rev (hd :: tl) = inv_rev( tl) ++ [(hd.fst, !hd.snd)] :=
begin
  sorry,
end

def word_reduced {x : free_group α} : reduce x.to_word = x.to_word := 
begin
  apply reduce.min,
  induction x,
  induction x,

  { finish, },

  unfold to_word,
  rw free_group.reduce.idem,

  { finish, },
end

def reduced_red {w : list (α × bool)} (h : reduce w = w) : red (reduce w) w :=
begin
  induction w,
  { finish, },
  { finish, },
end

def red_reduced {w : list (α × bool)} (h : red (reduce w) w) : reduce w = w :=
begin
  apply reduce.min,
  assumption,
end

def irreducible (w : list (α × bool)) : Prop := w.length = (reduce w).length

def irreducible_cons {hd : α × bool} {tl : list (α × bool)} (h : irreducible (hd :: tl)) : irreducible tl := 
begin
  sorry,
end

def reduced_irreducible {w : list (α × bool)} (h : reduce w = w) : irreducible w :=
begin
  have hl : w.length = w.length := rfl,
  nth_rewrite 1 ←h at hl,
  exact hl,
end

def rev_step_reduces {L₁ L₂ : list (α × bool)} (h : red.step L₁ L₂) : (red.step L₁.reverse L₂.reverse) :=
begin
  sorry, 
end

def list_inv (w : list (α × bool)) : list (α × bool) :=
 (list.map (λ (g : α × bool), (g.fst, !g.snd)) w) 

def inv_step_reduces {L₁ L₂ : list (α × bool)} (h : red.step L₁ L₂) : (red.step (list_inv L₁) (list_inv L₂)) :=
begin
  sorry, 
end

def rev_reduces {L₁ L₂ : list (α × bool)} (h : red L₁ L₂) : (red L₁.reverse L₂.reverse) :=
begin
  induction h with h1 h2 h3 h4,
  { finish, },
  have h5 := rev_step_reduces h4,
  apply red.trans,
  { exact h_ih, },
  exact red.step.to_red h5,
end


def irreducible_reduced {w : list (α × bool)} (h : irreducible w) : (reduce w = w) :=
begin
  have hr : red w (reduce w) := free_group.reduce.red,
  have hs := free_group.red.sublist hr,
  have hl := list.eq_of_sublist_of_length_eq hs h.symm,
  assumption,
end

def inv_rev_irreducible {w : list (α × bool)} (h : irreducible w) : irreducible (inv_rev w) :=
begin
  apply reduced_irreducible,
  apply  red_reduced,
  have k := inv_rev_reduces (reduced_red (irreducible_reduced h)),
  
  have h1 := irreducible_reduced h,
end


def inv_rev_reduced {w : list (α × bool)} (h : reduce w = w) : reduce (inv_rev w) = (inv_rev w) := irreducible_reduced $ inv_rev_irreducible $ reduced_irreducible h

def mk_word {w : list (α × bool)} (h : reduce w = w) : (mk w).to_word = w :=
begin
  rw ← h, 
  rw free_group.reduce.self,
  unfold to_word,
  simp,
end

def reduce_inv_rev {w : list (α × bool)} : reduce (inv_rev w) = inv_rev (reduce w) :=
begin
  have k : red w (reduce w) := reduce.red,
  have k2 := inv_rev_reduces k
--def inv_rev_reduces {L₁ L₂ : list (α × bool)} (h : red L₁ L₂) : (red (inv_rev L₁) (inv_rev L₂)) :=
end

def inv_to_word (x : free_group α) : (x⁻¹).to_word = inv_rev (x.to_word) :=
begin
  -- unfold to_word,
  induction x,
  { unfold to_word,
    simp,
    have h : reduce (inv_rev x) = inv_rev (reduce x),
    { sorry, },
    finish, },
  { finish, },
end

def inv_rev_reduces {L₁ L₂ : list (α × bool)} (h : red L₁ L₂) : (red (inv_rev L₁) (inv_rev L₂)) :=
begin
  unfold inv_rev,
  apply rev_reduces,
  
  induction h with h1 h2 h3 h4,
  { finish, },

  have h5 := inv_step_reduces h4,
  apply red.trans,
  { exact h_ih, },
  exact red.step.to_red h5,
end

def reduces_inv_rev {L₁ L₂ : list (α × bool)} (h : red (inv_rev L₁) (inv_rev L₂)) : (red L₁ L₂) :=
begin
  have h2 : red (inv_rev (inv_rev L₁)) (inv_rev (inv_rev L₂)) := inv_rev_reduces h,
  rw inv_rev_involutive at h2,
  rw inv_rev_involutive at h2,
  assumption,
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

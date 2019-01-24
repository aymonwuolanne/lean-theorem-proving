import analysis.topology.continuity
import category_theory.examples.topological_spaces
import analysis.real
import category_theory.limits.binary_products
import category_theory.examples.Top.products
import piecewise 
import order_aux

universe u
noncomputable theory

open category_theory.examples
open category_theory.limits
open category_theory

local attribute [instance] has_binary_product_of_has_product

@[reducible] def I := {x : ℝ // 0 ≤ x ∧ x ≤ 1}
def 𝕀 : Top := { α := I, str := by apply_instance}

-- proofs that 0, 1 and 2⁻¹ are contained in I
lemma I_contains_0 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := 
  ⟨le_refl 0, le_of_lt zero_lt_one⟩
lemma I_contains_1 : 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := 
  ⟨le_of_lt zero_lt_one, le_refl 1⟩

lemma two_inv_pos : 0 ≤ (2⁻¹ : ℝ) := le_of_lt (inv_pos two_pos) 
lemma two_inv_le_one : (2⁻¹ : ℝ) ≤ 1 := by rw [←one_div_eq_inv]; exact le_of_lt one_half_lt_one
lemma I_contains_half : 0 ≤ (2⁻¹ : ℝ) ∧ (2⁻¹ : ℝ) ≤ 1 := 
  ⟨two_inv_pos, two_inv_le_one⟩

-- shorthands for 0, 1 and 2⁻¹ as elements of I
def I_0    : I := ⟨ 0, I_contains_0 ⟩ 
def I_1    : I := ⟨ 1, I_contains_1 ⟩
def I_half : I := ⟨ 2⁻¹, I_contains_half ⟩

-- says that the path has initial point x and final point y
def path_prop {X : Top} (x y : X.α) (map : 𝕀 ⟶ X) : Prop := map.val I_0 = x ∧ map.val I_1 = y

structure path {X : Top} (x y : X.α) := 
(map : 𝕀 ⟶ X)
(property : path_prop x y map)

def const_map (X Y : Top) (y : Y.α) : X ⟶ Y := 
{ val := (λ x, y), 
  property := continuous_const }

-- a homotopy of paths is a map F from I × I → X such that 
--   F(s,0) = f
--   F(s,1) = g 
--   F(s,t) is a path from x to y for a fixed t
structure homotopy {X : Top} {x y : X.α} (f g : path x y) :=
  (F : limits.prod 𝕀 𝕀 ⟶ X)
  (left : prod.lift (𝟙 𝕀) (const_map 𝕀 𝕀 I_0) ≫ F = f.map)
  (right : prod.lift (𝟙 𝕀) (const_map 𝕀 𝕀 I_1) ≫ F = g.map)
  (endpts : ∀ t : I, path_prop x y (prod.lift (𝟙 𝕀) (const_map 𝕀 𝕀 t) ≫ F))

def homotopic {X : Top} {x y : X.α} (f g : path x y) := nonempty (homotopy f g)


namespace homotopic
-- we want to show that homotopic is an equivalence relation

-- given a map f this returns the homotopy from f to itself
def id_htpy {X : Top} (f : 𝕀 ⟶ X) : limits.prod 𝕀 𝕀 ⟶ X := limits.prod.fst 𝕀 𝕀 ≫ f

@[refl] theorem refl {X : Top} {x y : X.α} (f : path x y) : homotopic f f := ⟨ {
  F      := id_htpy f.map, 
  left   := by rw [id_htpy, ←category.assoc]; simp,
  right  := by rw [id_htpy, ←category.assoc]; simp,
  endpts := λ t, f.property
} ⟩

@[symm] theorem symm {X : Top} {x y : X.α} (f g : path x y) : homotopic f g → homotopic g f := sorry 

@[trans] theorem trans {X : Top} {x y : X.α} (f g h : path x y) : homotopic f g → homotopic g h → homotopic f h := 
sorry  

end homotopic


namespace I_lemmas

lemma in_I_of_le_half (x : I) (h : x.val ≤ 2⁻¹) : 0 ≤ 2 * x.val ∧ 2 * x.val ≤ 1 := 
  ⟨ zero_le_mul (le_of_lt two_pos) (x.property.left), 
  calc 
  2 * x.val ≤ 2 * 2⁻¹   : mul_le_mul_of_nonneg_left h (le_of_lt two_pos)
  ...       = 1         : mul_inv_cancel (ne_of_gt two_pos) ⟩

lemma in_I_of_ge_half (x : I) (h : x.val ≥ 2⁻¹) : 
  0 ≤ 2 * x.val - 1 ∧ 2 * x.val - 1 ≤ 1 := ⟨ 
    have h₁ : 2 * x.val ≥ 2 * 2⁻¹,
      from mul_le_mul_of_nonneg_left h (le_of_lt two_pos),
    calc 
      2 * x.val - 1 ≥ 2 * 2⁻¹ - 1   : add_le_add_right' h₁
      ...           = 1 - 1         : by rw [mul_inv_cancel (ne_of_gt two_pos)]
      ...           = 0             : sub_self 1,
    have h₁ : 2 * x.val ≤ 2 * 1, 
      from mul_le_mul_of_nonneg_left (x.property.right) (le_of_lt two_pos),
    calc 
      2 * x.val - 1 ≤ 2 * 1 - 1 : add_le_add_right' h₁
      ...           = 2 - 1       : by rw [mul_one]
      ...           = 1 + 1 - 1   : rfl
      ...           = 1 + (1-1)   : add_assoc 1 1 (-1)
      ...           = 1 + 0       : by rw [sub_self]
      ...           = 1           : add_zero 1
  ⟩  

lemma half_x_in_I (x : I) : 0 ≤ 2⁻¹ * x.val ∧ 2⁻¹ * x.val ≤ 1 := ⟨
  calc
    2⁻¹ * x.val ≥ 2⁻¹ * 0  : mul_le_mul_of_nonneg_left x.property.left two_inv_pos
    ...           = 0      : mul_zero 2⁻¹,
  calc 
    2⁻¹ * x.val ≤ 2⁻¹ * 1  : mul_le_mul_of_nonneg_left x.property.right two_inv_pos
    ...         = 2⁻¹      : mul_one 2⁻¹
    ...         ≤ 1        : two_inv_le_one
  ⟩ 

  lemma half_x_add_one_in_I (x : I) : 0 ≤ 2⁻¹ * (x.val + 1) ∧ 2⁻¹ * (x.val + 1) ≤ 1 := ⟨
  calc 
    2⁻¹ * (x.val + 1) = 2⁻¹*x.val + 2⁻¹*1    : left_distrib 2⁻¹ x.val 1
    ...                 = 2⁻¹ * x.val + 2⁻¹  : by rw [mul_one]
    ...                 ≥ 2⁻¹ * x.val + 0    : add_le_add_left two_inv_pos (2⁻¹ * x.val)
    ...                 = 2⁻¹ * x.val        : add_zero (2⁻¹ * x.val)
    ...                 ≥ 2⁻¹ * 0            : mul_le_mul_of_nonneg_left x.property.left two_inv_pos
    ...                 = 0                  : mul_zero 2⁻¹,
  have h₁ : x.val + 1 ≤ 1 + 1, 
    from add_le_add_right' x.property.right, 
  calc 
    2⁻¹ * (x.val + 1) ≤ 2⁻¹ * (1 + 1) : mul_le_mul_of_nonneg_left h₁ two_inv_pos
    ...               = 1             : inv_mul_cancel (ne_of_gt two_pos) 
 ⟩

lemma half_x_le_half (x : I) : 2⁻¹ * x.val ≤ 2⁻¹ := 
  calc 
    2⁻¹ * x.val ≤ (2⁻¹) * 1  : mul_le_mul_of_nonneg_left x.property.right two_inv_pos
    ...         = (2⁻¹)      : mul_one (2⁻¹)

lemma half_x_add_one_ge_half (x : I) : 2⁻¹ ≤ (2⁻¹) * (x.val + 1) := 
  have h₁ : 1 ≤ x.val + 1,
  from 
    calc
      x.val + 1 ≥ 0 + 1  : add_le_add_right' x.property.left 
      ...       = 1      : zero_add 1,
  calc 
    (2⁻¹) * (x.val + 1) ≥ (2⁻¹) * 1  : mul_le_mul_of_nonneg_left h₁ two_inv_pos
    ...                 = 2⁻¹        : mul_one (2⁻¹)

-- the inclusion of I into [0,2⁻¹]
def i₁ : I → I := λ x, ⟨ 2⁻¹ * x.val , half_x_in_I x ⟩

-- the inclusion of I into [2⁻¹, 1] 
def i₂ : I → I := λ x, ⟨ 2⁻¹ * (x.val + 1), half_x_add_one_in_I x ⟩

def i₁_inv (x : I) (hc : x.val ≤ 2⁻¹) : I := ⟨ 2 * x.val, in_I_of_le_half x hc ⟩

def i₂_inv (x : I) (hnc : x.val ≥ 2⁻¹) : I := ⟨ 2 * x.val - 1, in_I_of_ge_half x hnc ⟩

lemma comp_inv₁ (x : I) (hc : x ≤ I_half) : i₁ (i₁_inv x hc) = x := sorry 

lemma inv_comp₁ (x : I) : i₁_inv (i₁ x) (half_x_le_half x) = x := sorry 

lemma comp_inv₂ (x : I) (hnc : x ≥ I_half) : i₂ (i₂_inv x hnc) = x := sorry 

lemma inv_comp₂ (x : I) : i₂_inv (i₂ x) (half_x_add_one_ge_half x) = x := subtype.eq $
  calc 
    2 * (i₂ x).val - 1 = 2 * (2⁻¹ * (x + 1)) - 1  : rfl 
    ...                 = (2 * 2⁻¹) * (x + 1) - 1  : by rw [mul_assoc]
    ...                 = 1 * (x + 1) - 1          : by rw [mul_inv_cancel (ne_of_gt two_pos)]
    ...                 = x + 1 - 1                : by rw [one_mul] 
    ...                 = x + (1 - 1)              : add_assoc x 1 (-1)
    ...                 = x + 0                    : by rw [sub_self] 
    ...                 = x                        : add_zero x

end I_lemmas


open I_lemmas

-- the composition of two paths in X
def path_comp_map {X : Top} (f g : I → X.α) : I → X.α := 
  λ x, dite (x.val ≤ 2⁻¹)
    (f ∘ (i₁_inv x))
    (g ∘ (i₂_inv x) ∘ le_of_lt ∘ lt_of_not_ge)

def val : I → ℝ := subtype.val 

def double : ℝ → ℝ := λ x, 2 * x 

lemma cont1 : continuous double := continuous_mul continuous_const continuous_id

def double_sub_one : ℝ → ℝ := λ x, 2*x - 1

lemma cont2 : continuous double_sub_one := continuous_sub cont1 continuous_const

lemma I_self_pushout : ∀ {s : set I}, is_open (i₁ ⁻¹' s) → is_open (i₂ ⁻¹' s) → is_open s :=  
  λ s hs1 hs2,
  have h₁ : ∃ t₁, is_open t₁ ∧ i₁ ⁻¹' s = val ⁻¹' t₁,
    from is_open_induced_iff.mp hs1,
  have h₂ : ∃ t₂, is_open t₂ ∧ i₂ ⁻¹' s = val ⁻¹' t₂,
    from is_open_induced_iff.mp hs2, 
  is_open_induced_iff.mpr $
    exists.elim h₁ $ λ t₁ ht₁, exists.elim h₂ $ λ t₂ ht₂,
      let t := (double ⁻¹' t₁) ∪ (double_sub_one ⁻¹' t₂) in
      ⟨t,
      have hopen : is_open t,
        from is_open_union (cont1 t₁ ht₁.left) (cont2 t₂ ht₂.left), 
      have heq : s = val ⁻¹' t,
        from sorry,
      ⟨hopen, heq⟩
      ⟩

lemma commutes_1 {X : Top} (f g : I → X.α) (h : f I_1 = g I_0) : path_comp_map f g ∘ i₁ = f := 
funext $ λ x, 
  have h₁ : (path_comp_map f g ∘ i₁) x = f (i₁_inv (i₁ x) (half_x_le_half x)), 
    from dif_pos (half_x_le_half x), 
  have h₂ : f (i₁_inv (i₁ x) (half_x_le_half x)) = f x,
    from congr_arg f (inv_comp₁ x),
  trans h₁ h₂
  
lemma commutes_2 {X : Top} (f g : I → X.α) (h : f I_1 = g I_0) : path_comp_map f g ∘ i₂ = g := 
funext $ λ x,
  have h₁ : i₂ x ≥ I_half,
    from half_x_add_one_ge_half x,
  or.elim (eq_or_lt_of_le h₁) 
    ( λ heq,
    have heq₁ : i₂ x ≤ I_half, 
      from le_of_eq (symm heq),
    have heq₅ : x = I_0,  
      from subtype.eq $ 
        have h₁ : 1 = x.val + 1, 
          from calc 
            (1:ℝ) = 2 * 2⁻¹                   : symm (mul_inv_cancel (ne_of_gt two_pos))
            ...   = 2 * (2⁻¹ * (x.val + 1))   : congr_arg (has_mul.mul 2) (subtype.ext.mp heq)
            ...   = (2 * 2⁻¹) * (x.val + 1)   : symm (mul_assoc 2 (2⁻¹) (x.val + 1))
            ...   = 1 * (x.val + 1)           : by rw [mul_inv_cancel (ne_of_gt two_pos)]
            ...   = x.val + 1                 : one_mul (x.val + 1),
        calc 
          x.val = x.val + 0       : symm (add_zero x.val)
          ...   = x.val + (1 - 1) : by rw [sub_self] 
          ...   = x.val + 1 - 1   : symm (add_assoc x.val 1 (-1))
          ...   = 1 - 1           : by rw [←h₁]
          ...   = 0               : sub_self 1,
    have heq₂ : (path_comp_map f g ∘ i₂) x = f (i₁_inv (i₂ x) heq₁),
      from dif_pos heq₁,
    begin
    rw [heq₂],
    have heq₃ : 2 * (i₂ x).val = 1,
      calc 
        2 * (i₂ x).val = 2 * (I_half).val : by rw [heq] 
        ...             = 2 * (2⁻¹)        : rfl 
        ...             = 1                : mul_inv_cancel (ne_of_gt two_pos), 
    have heq₄ : f (i₁_inv (i₂ x) heq₁) = f I_1, 
      exact congr_arg f (subtype.eq heq₃),
    rw [heq₄, heq₅],
    exact h
    end )

    (λ hlt,
    have hlt₁ : ¬ (i₂ x) ≤ I_half,
      from not_le_of_gt hlt,
    have h₂ : (path_comp_map f g ∘ i₂) x = g (i₂_inv (i₂ x) h₁),
      from dif_neg (not_le_of_gt hlt),
    have h₄ : g (i₂_inv (i₂ x) h₁) = g x,
      from congr_arg g (inv_comp₂ x), 
    trans h₂ h₄
    )

lemma path_comp_continuous {X : Top} (f g : I → X.α) (hf : continuous f) (hg : continuous g)
  (h : f I_1 = g I_0) : continuous (path_comp_map f g) := begin
    intros s hs,
    have h₁ : is_open (i₁ ⁻¹' (path_comp_map f g ⁻¹' s)), 
      have h₁₂ : i₁ ⁻¹' (path_comp_map f g ⁻¹' s) = path_comp_map f g ∘ i₁ ⁻¹' s := rfl,
      rw [h₁₂, commutes_1 f g h], 
      exact hf s hs,
    have h₂ : is_open (i₂ ⁻¹' (path_comp_map f g ⁻¹' s)), 
      have h₂₂ : i₂ ⁻¹' (path_comp_map f g ⁻¹' s) = path_comp_map f g ∘ i₂ ⁻¹' s := rfl,
      rw [h₂₂, commutes_2 f g h],
      exact hg s hs,
    exact I_self_pushout h₁ h₂
  end

-- this defines the type of homotopy classes of paths from x to y
def htpy_class {X : Top} (x y : X.α) := quot (@homotopic X x y) 

-- to define the fundamental group(oid) we need to instantiate the category of paths in X
-- with homotopy classes of paths as morphisms between each point. 
def paths (X : Top) := X.α 

-- TODO
def path_composition {X : Top} {x y z : paths X} (f : path x y) (g : path y z) : path x z := {
  map := {val := path_comp_map f.map g.map, 
    property := path_comp_continuous f.map.val g.map.val f.map.property g.map.property 
      (trans f.property.right (symm g.property.left) )
      }, 
  property := sorry
} 

-- [f][g] = [fg]
def composition {X : Top} {x y z : paths X} (f : path x y) : htpy_class y z → htpy_class x z := 
  quot.lift 
    (λ g, quot.mk (@homotopic X x z) (path_composition f g)) 
    (λ a b (h : homotopic a b), quot.sound sorry)
  -- want h : quot.mk (@homotopic X x z) (path_composition f a) = quot.mk (@homotopic X x z) (path_composition f b)
  -- using quot.sound it is enough to have 
  -- h : homotopic (path_composition f a) (homotopic path_composition f b)
  -- TODO ^that

instance (X : Top) : category (paths X) := {
  hom      := λ x y, htpy_class x y, 
  id       := λ x, quot.mk (λ f g, homotopic f g) 
    { map := const_map 𝕀 X x, property := by tidy },
  comp     := sorry,
  assoc'   := sorry, 
  comp_id' := sorry, 
  id_comp' := sorry
  } 

def fundamental_group (X : Top) (x : paths X) : Type := sorry 
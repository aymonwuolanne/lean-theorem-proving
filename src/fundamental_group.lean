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
open set

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

@[simp] lemma I_0_val : I_0.val = 0 := rfl

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

namespace path_comp

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

def double : ℝ → ℝ := λ x, 2 * x 

lemma cont1 : continuous double := continuous_mul continuous_const continuous_id

def double_sub_one : ℝ → ℝ := λ x, 2*x - 1

lemma cont2 : continuous double_sub_one := continuous_sub cont1 continuous_const

def s := {x : I | x.val ≤ 2⁻¹}

instance : decidable_pred s := λ x : I, has_le.le.decidable (x.val) 2⁻¹

lemma closure1 : closure s = {x : I | x.val ≤ 2⁻¹} := 
   (closure_le_eq continuous_induced_dom continuous_const)

lemma closure2 : closure (-s) ⊆ {x : I | x.val ≥ 2⁻¹} :=
  have h₁ : -s ⊆ {x : I | x.val ≥ 2⁻¹},
    from assume x hx, 
    have h₁ : x.val > 2⁻¹,
      from lt_of_not_ge hx,
    le_of_lt h₁,
  have h₂ : is_closed {x : I | x.val ≥ 2⁻¹},
    from is_closed_le continuous_const continuous_induced_dom,
  closure_minimal h₁ h₂

def first_half : subtype (closure s) → I := λ x, 
  have h: x.val ∈ {x : I | x.val ≤ 2⁻¹}, 
    from (subset.antisymm_iff.mp closure1).left x.property,
  ⟨ double x.val.val, in_I_of_le_half x.val h ⟩

def second_half : subtype (closure (-s)) → I := λ x,
  have h : x.val ∈ {x : I | x.val ≥ 2⁻¹},
    from closure2 x.property,
  ⟨ double_sub_one x.val.val, in_I_of_ge_half x.val h ⟩

lemma cont_first_half : continuous first_half := 
  continuous_induced_rng $
  have h : subtype.val ∘ first_half = double ∘ subtype.val ∘ subtype.val, 
    from rfl,
  by rw [h]; exact continuous.comp 
    (continuous.comp continuous_induced_dom continuous_induced_dom) 
    cont1

lemma cont_second_half : continuous second_half := 
  continuous_induced_rng $ 
  have h : subtype.val ∘ second_half = double_sub_one ∘ subtype.val ∘ subtype.val,
    from rfl, 
  by rw [h]; exact continuous.comp 
    (continuous.comp continuous_induced_dom continuous_induced_dom)
    cont2

def path_comp_map {X : Top} (f g : I → X.α) : I → X.α := pw (f ∘ first_half) (g ∘ second_half)

lemma computation1 {x : I} (h : x.val = 2⁻¹) : double x.val = 1 := by rw [h]; exact mul_inv_cancel (ne_of_gt two_pos) 

lemma computation2 {x : I} (h : x.val = 2⁻¹) : double_sub_one x.val = 0 := by rw [h]; exact
  have h : (2 : ℝ) * 2⁻¹ = 1 := mul_inv_cancel (ne_of_gt two_pos), 
  calc 
    (2 : ℝ) * 2⁻¹ - 1 = 1 - 1  : by rw [h]
    ...               = 0      : sub_self 1

theorem path_comp_continuous {X : Top} (f g : I → X.α) (hf : continuous f) (hg : continuous g)
  (h : f I_1 = g I_0) : continuous (path_comp_map f g) := begin 
    have hp : ∀ x hx, 
      (f ∘ first_half) ⟨x, frontier_subset_closure hx⟩ = (g ∘ second_half) ⟨x, frontier_subset_closure_compl hx⟩,
      intros x hx,
      have h₁ : frontier s ⊆ {x : I | x.val = 2⁻¹},
        from frontier_le_subset_eq continuous_induced_dom continuous_const,
      have hf1 : first_half ⟨x, frontier_subset_closure hx⟩ = I_1,
        have : double x.val = 1,
          from computation1 (h₁ hx),
        exact subtype.eq this,
      have hg0 : second_half ⟨x, frontier_subset_closure_compl hx⟩ = I_0,
        have : double_sub_one x.val = 0,
          from computation2 (h₁ hx),
        exact subtype.eq this,
      simp [hf1, hg0, h],

    exact continuous_pw (f ∘ first_half) (g ∘ second_half) 
      hp (continuous.comp cont_first_half hf) (continuous.comp cont_second_half hg),
  end

end path_comp

open path_comp

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

lemma path_comp_associative {X : Top} {x₀ x₁ x₂ x₃ : paths X} (f : path x₀ x₁) (g : path x₁ x₂)
  (h : path x₂ x₃) : 
  homotopic (path_composition f (path_composition g h)) (path_composition (path_composition f g) h) := 
  sorry

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
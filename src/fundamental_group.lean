import analysis.topology.continuity
import category_theory.examples.topological_spaces
import analysis.real
import category_theory.limits.binary_products
import category_theory.examples.Top.products
import category_theory.groupoid
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

-- proofs that 0, 1 and 1/2 are contained in I
lemma I_contains_0 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := 
  ⟨le_refl 0, le_of_lt zero_lt_one⟩
lemma I_contains_1 : 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := 
  ⟨le_of_lt zero_lt_one, le_refl 1⟩
lemma I_contains_half : 0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1 := 
  ⟨le_of_lt one_half_pos, le_of_lt one_half_lt_one⟩
-- shorthands for 0, 1 and 1/2 as elements of I
def I_0    : I := ⟨ 0, I_contains_0 ⟩ 
def I_1    : I := ⟨ 1, I_contains_1 ⟩
def I_half : I := ⟨ 1/2, I_contains_half ⟩

-- says that the path has initial point x and final point y
def path_prop {X : Top} (x y : X.α) (map : 𝕀 ⟶ X) : Prop := map.val I_0 = x ∧ map.val I_1 = y

structure path {X : Top} (x y : X.α) := 
(map : 𝕀 ⟶ X)
(property : path_prop x y map)

def const_map (X Y : Top) (y : Y.α) : X ⟶ Y := 
{ val := (λ x, y), 
  property := continuous_const }

lemma in_I_of_le_half (x : I) (h : x.val ≤ 1/2) : 0 ≤ 2 * x.val ∧ 2 * x.val ≤ 1 := 
  ⟨ zero_le_mul (le_of_lt two_pos) (x.property.left), 
  calc 
  2 * x.val ≤ 2 * (1/2) : mul_le_mul_of_nonneg_left h (le_of_lt two_pos)
  ...       = 2 * 2⁻¹   : by rw [one_div_eq_inv]
  ...       = 1         : mul_inv_cancel (ne_of_gt two_pos) ⟩

lemma in_I_of_gt_half (x : I) (h : x.val > 1/2) : 
  0 ≤ 2 * x.val - 1 ∧ 2 * x.val - 1 ≤ 1 := 
  begin 
    apply and.intro, 
    have h₁ : 2 * x.val ≥ 2 * (1/2),
      from mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt two_pos),
    calc 
      2 * x.val - 1 ≥ 2 * (1/2) - 1 : add_le_add_right' h₁
      ...           = 2 * 2⁻¹ - 1   : by rw [one_div_eq_inv]
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
  end  

instance : decidable_linear_order I := by apply_instance

def loop_composition {X : Type} (f : I → X) (g : I → X) : I → X := 
  λ x, dite (x ≤ I_half)
       (λ hc, f ⟨2 * x.val, in_I_of_le_half x hc⟩)
       (λ hnc, g ⟨2 * x.val - 1, in_I_of_gt_half x (lt_of_not_ge' hnc)⟩)

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
  F := id_htpy f.map, 
  left := by rw [id_htpy, ← category.assoc]; simp,
  right := by rw [id_htpy, ←category.assoc]; simp,
  endpts := λ t, f.property
} ⟩

@[symm] theorem symm {X : Top} {x y : X.α} (f g : path x y) : homotopic f g → homotopic g f := sorry 

@[trans] theorem trans {X : Top} {x y : X.α} (f g h : path x y) : homotopic f g → homotopic g h → homotopic f h := 
sorry  

end homotopic

-- this defines the type of homotopy classes of paths from x to y
def htpy_class {X : Top} (x y : X.α) := quot (@homotopic X x y) 

-- to define the fundamental group(oid) we need to instantiate the category of paths in X
-- with homotopy classes of paths as morphisms between each point. 
def paths (X : Top) := X.α 

-- TODO
def path_composition {X : Top} {x y z : paths X} (f : path x y) (g : path y z) : path x z := sorry 

-- [f][g] = [fg]
def composition {X : Top} {x y z : paths X} (f : path x y) : htpy_class y z → htpy_class x z := quot.lift 
  (λ g, quot.mk (@homotopic X x z) (path_composition f g)) 
  (λ a b (h : homotopic a b), quot.sound sorry)
  -- want h : quot.mk (@homotopic X x z) (path_composition f a) = quot.mk (@homotopic X x z) (path_composition f b)
  -- using quot.sound it is enough to have 
  -- h : homotopic (path_composition f a) (homotopic path_composition f b)
  -- TODO ^that

instance (X : Top) : category (paths X) := { 
  hom := λ x y, htpy_class x y, 
  id := λ x, quot.mk (λ f g, homotopic f g) { map := const_map 𝕀 X x, property := by tidy }, 
  comp := sorry,
  assoc' := sorry, 
  comp_id' := sorry, 
  id_comp' := sorry
  } 

instance (X : Top) : groupoid (paths X) := sorry 

def fundamental_group (X : Top) (x : paths X) : Type := Aut x
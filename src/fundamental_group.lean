import analysis.topology.continuity
import category_theory.examples.topological_spaces
import analysis.real
import category_theory.limits.binary_products
import category_theory.examples.Top.products


noncomputable theory

open category_theory.examples
open category_theory.limits
open category_theory

local attribute [instance] has_binary_product_of_has_product
def I := {x : ℝ | 0 ≤ x ∧ x ≤ 1} 
def 𝕀 : Top := { α := I }

def path (X : Top) := 𝕀 ⟶ X

-- proofs that 0 and 1 are contained in I
lemma I_contains_0 : (0 : ℝ) ∈ I := 
⟨le_refl 0, le_of_lt zero_lt_one⟩
lemma I_contains_1 : (1 : ℝ) ∈ I := 
⟨le_of_lt zero_lt_one, le_refl 1⟩
-- shorthands for 0 and 1 as elements of I
def I_0 : I := ⟨ 0, I_contains_0 ⟩ 
def I_1 : I := ⟨ 1, I_contains_1 ⟩


-- TODO define `path x y`, define `loop_at x = path x x`, and `free_loop = Σ x, loop_at x`
-- TODO? Define the path category
-- def paths (X : Top) := X.α
-- instance category (paths X) :=
-- { hom := λ x y, path x y }
-- If `C` is a category, `x : C`, `Aut x` is a group.

-- loops are paths that have the same endpoints
def is_loop {X : Top} (γ : path X) := γ.val I_0 = γ.val I_1 
def loop (X : Top) := subtype (@is_loop X) -- TODO custom structure


-- defining the constant map to the interval
def const_hom {X : Top} (a : I) : (X ⟶ 𝕀) := {val := (λ x, a), property := continuous_const}


-- intuitively says that F(x,0) = f(x) and F(x,1) = g(x) for all x ∈ X. 
def homotopy {X Y : Top} (f g : X ⟶ Y) (F : limits.prod X 𝕀 ⟶ Y) : Prop :=  
 prod.lift (𝟙 X) (const_hom I_0) ≫ F = f 
 ∧ 
 prod.lift (𝟙 X) (const_hom I_1) ≫ F = g 
 

def loop_homotopy {X : Top} (f g : loop X) (F : limits.prod 𝕀 𝕀 ⟶ X) : Prop :=  
homotopy f.val g.val F 
∧ 
∀ a : I, is_loop (prod.lift (𝟙 𝕀) (const_hom a) ≫ F) 


def homotopic {X : Top} (f g : loop X) : Prop := ∃ (F : limits.prod 𝕀 𝕀 ⟶ X), loop_homotopy f g F 

--       fst   f
-- 𝕀 × 𝕀  ⟶ 𝕀 ⟶ X 
def id_htpy {X : Top} (f : 𝕀 ⟶ X) : limits.prod 𝕀 𝕀 ⟶ X := limits.prod.fst 𝕀 𝕀 ≫ f

-- lemma id_htpy_is_htpy {X : Top} (f : path X): homotopy f f (id_htpy f) := 
-- begin
--   apply and.intro, 
--   rw [id_htpy, ←category.assoc, limits.prod.lift_fst, category.id_comp],
--   rw [id_htpy, ←category.assoc, limits.prod.lift_fst, category.id_comp]
-- end
-- #print id_htpy_is_htpy

namespace homotopic
-- we want to show that 'homotopic' is an equivalence relation
@[refl] theorem refl {X : Top} (f : loop X) : homotopic f f := 
⟨ id_htpy f.val, by tidy ⟩ 

-- begin 
--   use id_htpy f.val,
--   -- show loop_homotopy f f (id_htpy f.val),
--   tidy {trace_result := tt},
-- end

@[symm] theorem symm : ∀ {X : Top} (f g : loop X), homotopic f g → homotopic g f := sorry 

@[trans] theorem trans : ∀ {X : Top} (f g h : loop X), homotopic f g → homotopic g h → homotopic f h := sorry  
end homotopic
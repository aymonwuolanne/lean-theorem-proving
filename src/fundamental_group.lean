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

structure path {X : Top} (x y : X.α) := 
(map : 𝕀 ⟶ X) (cont : continuous map) (property : map.val I_0 = x ∧ map.val I_1 = y) 

def loop_at {X : Top} (x : X.α) := path x x

def const_map (X Y : Top) (y : Y.α) : X ⟶ Y := {val := (λ x, y), property := continuous_const}

def loop_composition {X : Top} {x y z : X.α} (f : path x y) (g : path y z) : path x z := sorry 

def paths (X : Top) := X.α 
instance {X : Top} : category (paths X) := { 
    hom := λ x y, path x y, 
    id := λ x, { map := const_map 𝕀 X x, cont := continuous_const, property := by tidy}, 
    comp := @loop_composition X } 

def fundamental_group (X : Top) (x : paths X) := category_theory.Aut x



-- intuitively says that F(x,0) = f(x) and F(x,1) = g(x) for all x ∈ X. 
def homotopy {X Y : Top} (f g : X ⟶ Y) (F : limits.prod X 𝕀 ⟶ Y) : Prop :=  
 prod.lift (𝟙 X) (const_map X 𝕀 I_0) ≫ F = f 
 ∧ 
 prod.lift (𝟙 X) (const_map X 𝕀 I_1) ≫ F = g 
 

def loop_homotopy {X : Top} {x : X.α} (f g : loop_at x) (F : limits.prod 𝕀 𝕀 ⟶ X) : Prop :=  
homotopy f.map g.map F 
∧ 
∀ a : I, (prod.lift (𝟙 𝕀) (const_map 𝕀 𝕀 a) ≫ F)


def homotopic {X : Top} {x : X.α} (f g : loop_at x) : Prop := ∃ (F : limits.prod 𝕀 𝕀 ⟶ X), loop_homotopy f g F 

-- given a map f this returns the homotopy from f to itself
def id_htpy {X : Top} (f : 𝕀 ⟶ X) : limits.prod 𝕀 𝕀 ⟶ X := limits.prod.fst 𝕀 𝕀 ≫ f

namespace homotopic
-- we want to show that 'homotopic' is an equivalence relation
@[refl] theorem refl {X : Top} {x : X.α} (f : loop_at x) : homotopic f f := 
⟨ id_htpy f.map, sorry ⟩ 

@[symm] theorem symm {X : Top} {x : X.α} (f g : loop_at x) :homotopic f g → homotopic g f := sorry 

@[trans] theorem trans {X : Top} {x : X.α} (f g h : loop_at x) : homotopic f g → homotopic g h → homotopic f h := 
sorry  

end homotopic


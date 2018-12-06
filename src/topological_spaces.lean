import analysis.topology.continuity
import category_theory.examples.topological_spaces
import analysis.real
import analysis.normed_space
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

-- proving that 0 and 1 are in fact contained in I
lemma I_contains_0 : (0 : ℝ) ∈ I := 
⟨le_refl 0, le_of_lt zero_lt_one⟩
lemma I_contains_1 : (1 : ℝ) ∈ I := 
⟨le_of_lt zero_lt_one, le_refl 1⟩
-- shorthands for 0 and 1 as elements of I
def I_0 : I := ⟨ 0, I_contains_0 ⟩ 
def I_1 : I := ⟨ 1, I_contains_1 ⟩

-- loops are defined as paths that have the same endpoints
def loop (X : Top) := subtype (λ (γ : path X), γ.val I_0 = γ.val I_1)


def homotopy {X Y : Top} (f g : X ⟶ Y) := {F : limits.prod X 𝕀 ⟶ Y // true }

def constant_0 (X : Top) := λ (x : X.α), 0 
def constant_1 (X : Top) := λ (x : X.α), 1




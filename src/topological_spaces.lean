import analysis.topology.continuity
import category_theory.examples.topological_spaces
import analysis.real
import analysis.normed_space
import category_theory.limits.binary_products
import category_theory.examples.Top.products


noncomputable theory

def I := { x : ℝ | 0 ≤ x ∧ x ≤ 1 }
 
instance : topological_space I := by apply_instance

open category_theory.examples
open category_theory

def 𝕀     : Top := { α := I }
def s : Top := { α := punit, str := sorry } -- use the discrete topology

def path (X : Top) := 𝕀 ⟶ X


-- defining S¹
def S1 := { x : ℝ × ℝ | norm x = 1}

-- S¹ as a category
def 𝕊1 : Top := { α := S1 }

-- loops are defined as continuous maps from S1 to the space X
inductive loop (X : Top) : Type := 𝕊1 ⟶ X

def prd (X Y : Top) : Top := 
limits.pi (limits.two.map X Y)

-- def homotopy {X Y : Top} (f g : X ⟶ Y) := {F : limits.prod X 𝕀 ⟶ Y // true }
-- set_option trace.class_instances true
def right_unitor (X : Top) : X ⟶ prd X s :=
{ val := λ x, begin intros, cases b, exact x, exact punit.star end,
  property := begin end
}

def prd' (X Y : Top) : Top :=
{ α := X.α × Y.α }

def right_unitor' (X : Top) : X ⟶ prd' X s :=
{ val := λ x, (x, punit.star),
  property := begin end } 
  -- this should just be because the topology on the product is by definitoin
  -- the topology so that pairs of continuous maps constitute a continuous map to the product!



-- example instantiating ℕ with the discrete topology from basics
open set

-- define every subset of ℕ to be open
def nat_isopen : set ℕ → Prop := (λ (S : set ℕ), true)
-- prove the relevant properties of a topological space 
def nat_isopen_univ : nat_isopen univ := trivial
def nat_isopen_inter : ∀ s t, nat_isopen s → nat_isopen t → nat_isopen (s ∩ t) := 
λ s t, (λ hs ht, trivial)
def nat_isopen_sUnion : ∀ s, (∀ t ∈ s, nat_isopen t) → nat_isopen (⋃₀ s) := 
λ s, (λ h, trivial)

instance nat_top  : topological_space ℕ := 
⟨ nat_isopen, nat_isopen_univ, nat_isopen_inter, nat_isopen_sUnion ⟩

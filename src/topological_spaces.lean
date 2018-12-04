import data.analysis.topology
import analysis.topology.continuity
import analysis.topology.continuous_map
import category_theory.examples.topological_spaces
import data.real.basic
import analysis.real

noncomputable theory

def I := { x : ℝ | 0 ≤ x ∧ x ≤ 1 }
 
def foo : topological_space I := by apply_instance

open category_theory.examples

def 𝕀 : Top := { α := I }

def path (X : Top) := 𝕀 ⟶ X

#check path

#print I


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

instance nat_top : topological_space ℕ := 
⟨nat_isopen, nat_isopen_univ, nat_isopen_inter, nat_isopen_sUnion⟩

 
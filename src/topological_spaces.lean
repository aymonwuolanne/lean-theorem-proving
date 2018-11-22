import data.analysis.topology
import analysis.topology.continuity
import analysis.topology.continuous_map
import category_theory.examples.topological_spaces
import data.real.basic
import analysis.real

noncomputable theory

example : topological_space ℝ := by apply_instance

def I := { x : ℝ | 0 ≤ x ∧ x ≤ 1 }
 
def foo : topological_space I := by apply_instance

structure path (X : Type) [topological_space X] :=
(γ : I → X)
(w : continuous γ)

def path' (X : Type) [topological_space X] := continuous_map I X

open category_theory.examples

def 𝕀 : Top := { α := I }

def path'' (X : Top) := 𝕀 ⟶ X

#check path''

#print subtype.topological_space
#print foo

#print I
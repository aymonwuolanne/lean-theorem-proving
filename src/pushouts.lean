import category_theory.examples.topological_spaces
import category_theory.limits.pullbacks
import category_theory.const 
import analysis.topology.continuity

open category_theory.examples 
open category_theory.limits 
open category_theory.functor
open category_theory
open sum

universe u
noncomputable theory 

variables {X Y Z : Top.{u}}
variables (f : X ⟶ Y) (g : X ⟶ Z)

-- in the following diagram P is the pushout we wish to construct
-- X  ⟶  Y 
-- ↓      ↓ 
-- Z  ⟶  P 

-- this relation identifies any x and y that are the image of the same 
-- point in X
def r (x : sum Y.α Z.α) (y : sum Y.α Z.α) : Prop := 
x = y ∨ 
∃ a : X.α, inl (f.val a) = x ∧ inr (g.val a) = y

def P : Top := { α := quot (r f g), str := by apply_instance}

-- inclusion maps from Y and Z into the pushout P
def i_Y : Y ⟶ P f g := { val := quot.mk (r f g) ∘ inl, 
    property := continuous.comp continuous_inl continuous_quot_mk }
def i_Z : Z ⟶ P f g := { val := quot.mk (r f g) ∘ inr, 
    property := continuous.comp continuous_inr continuous_quot_mk }

lemma natural : f ≫ (i_Y f g) = g ≫ (i_Z f g) := 
subtype.eq 
begin 
  rw [concrete_category_comp, i_Y, i_Z],
  dsimp, 
  ext, 
  rw [function.comp.assoc], 
  apply quot.sound,
  exact or.inr ⟨ x, ⟨ rfl, rfl ⟩ ⟩,
end 

def Top.nat_trans_app (A : walking_span) : (span f g).obj A ⟶ ((const walking_span).obj (P f g)).obj A :=
    match A with 
| walking_span.zero  := f ≫ (i_Y f g)
| walking_span.left  := i_Y f g
| walking_span.right := i_Z f g
end

def Top.nat_trans : span f g ⟹ (const walking_span).obj (P f g) := { app := Top.nat_trans_app f g, 
naturality' := sorry }

def topcat : category Top := by apply_instance 

-- cosquare := λ f g, something of type cocone (span f g)
-- span f g is a functor from walking_span.{v} to Top
-- cocone (F : J ⥤ Top) is a structure taking an object X : Top and 
-- a natural transformation ι taking F to (const J).obj X
-- natural transformations have an app field and a naturality' field
instance toppush : @has_pushouts Top topcat := { cosquare := sorry,
is_pushout := sorry }  
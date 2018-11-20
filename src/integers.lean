namespace hidden
inductive natural : Type
| zero : natural
| s : natural → natural

open natural

def add (a b : natural) : natural := 
natural.rec_on b a (λ b add_a_b, s add_a_b)

def mul (a b : natural) : natural := 
natural.rec_on b zero (λ b mul_a_b, add mul_a_b a)

instance : has_add natural := has_add.mk add 
instance : has_mul natural := has_mul.mk mul 


theorem add_assoc : ∀ (a b c : natural), a + (b + c) = (a + b) + c := 
begin
  intros a b c, 
  induction c,
    refl,                -- zero case 

    have h₁ : a + (b + s c_a) = s (a + (b + c_a)), 
    refl, 
    have h₂ : a + b + s c_a = s (a + b + c_a),
    refl,
    rw [h₁, h₂, c_ih]
end

-- to show that adding zero on the left gives the same result
lemma add_zero : ∀ a : natural, zero + a = a := 
begin
  intro a,
  induction a with a,
    refl, 

    have h₁ : zero + s a = s (zero + a), 
    refl, 
    rw [h₁, a_ih]
end


lemma l2 : ∀ (a b : natural), s (b + a) = (s b) + a := 
begin 
  intros a b, 
  induction a with a, 
    refl,
  
    have h₁ : b + s a = s (b + a), 
    refl, 
    have h₂ : s b + s a = s (s b + a), 
    refl, 
    rw [h₁, h₂, a_ih]
end

-- commutativity of addition
theorem add_comm : ∀ (a b : natural), a + b = b + a := 
begin 
  intros a b, 
  induction b with b, 
    rw add_zero, 
    refl, 

    have h₁ : a + s b = s (a + b),
    refl, 
    rw [h₁, b_ih], 
    apply l2
end 

theorem distributivity : ∀ (a b c : natural), a * (b + c) = a*b + a*c := 
begin
  intros a b c, 
  induction c with c, 
    refl, 
    
    have h₁ : b + s c = s (b + c), 
    refl, 
    have h₂ : a * s (b + c) = a * (b + c) + a, 
    refl, 
    have h₃ : a * b + a * s c = a * b + (a * c + a), 
    refl,
    rw [h₁, h₂, h₃, add_assoc, c_ih]
end


end hidden
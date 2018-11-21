namespace hidden
inductive natural : Type
| zero : natural
| s : natural → natural

open natural

def add : natural → natural → natural 
| a zero  := a 
| a (s b) := s (add a b)


def mul : natural → natural → natural 
| a zero  := zero 
| a (s b) := add (mul a b) a

instance : has_add natural := has_add.mk add 
instance : has_mul natural := has_mul.mk mul 


theorem add_assoc : ∀ (a b c : natural), a + (b + c) = (a + b) + c := 
begin
  intros a b c, 
  induction c,
    refl,                

    have h₁ : a + (b + s c_a) = s (a + (b + c_a)), 
    refl, 
    have h₂ : a + b + s c_a = s (a + b + c_a),
    refl,
    rw [h₁, h₂, c_ih]
end

-- adding zero on the left gives the same result
lemma add_zero : ∀ a : natural, zero + a = a := 
begin
  intro a,
  induction a with a,
    refl, 

    have h₁ : zero + s a = s (zero + a), 
    refl, 
    rw [h₁, a_ih]
end

-- a lemma that helps in proving the commutativity of addition
lemma l₁ : ∀ (a b : natural), s (b + a) = (s b) + a := 
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


theorem add_comm : ∀ (a b : natural), a + b = b + a := 
begin 
  intros a b, 
  induction b with b, 
    rw add_zero, 
    refl, 

    have h₁ : a + s b = s (a + b),
    refl, 
    rw [h₁, b_ih], 
    apply l₁
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
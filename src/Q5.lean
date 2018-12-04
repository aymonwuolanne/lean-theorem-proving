import data.nat.prime 
open nat 
 

example : ¬ (prime 4) := 
begin 
    apply not.intro, 
    intro h, 
    have h₂ : 2 ∣ 4, 
    apply dvd.intro 2,
    refl, 

    have h₃ : 2 ∣ 4 → 2=1 ∨ 2=4, 
    apply (and.right h),
    have h₄ : 2=1 ∨ 2=4, 
    apply h₃, from h₂, 
    cases h₄,
    cases h₄,
    cases h₄, 
end 

example : prime 5 := 
begin 
  apply and.intro, 
    have h₁ : 2 + 3 = 5, from rfl, 
    apply le.intro h₁, 

    intros m h, 
    have h1 : 1 ∣ 5, from sorry,
    have h2 : ¬ (2 ∣ 5), from sorry, 
    have h3 : ¬ 3 ∣ 5, from sorry, 
    have h4 : ¬ 4 ∣ 5, from sorry, 
    have h5 : 5 ∣ 5, from sorry, 

    
    
end


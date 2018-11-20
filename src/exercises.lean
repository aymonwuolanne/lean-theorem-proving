
-- ch2
    universe u 

    -- problem 1
    def double (x : ℕ) := x + x 
    def square (x : ℕ) := x*x
    def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
    def Do_twice (f : (ℕ → ℕ) → (ℕ → ℕ)) (g: ℕ → ℕ) := f (f g) 
    
    #eval double (do_twice double 10)
    #eval Do_twice do_twice double 2


    -- problem 2
    def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := 
        let g (x : α) (y : β) := f (x,y) in g

    def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := 
        let g (x : α × β) := f x.1 x.2 in g

    -- problem 3
    namespace vec
        constant vec         : Type u → ℕ → Type u

        constant vec_add     : Π {n : ℕ}, vec ℕ n → vec ℕ n → vec ℕ n
        constant vec_reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n

        -- some example checks
        constant v1 : vec ℕ 5
        constant v2 : vec ℕ 5
        #check vec_add v1 v2 
        #check vec_reverse v1

    end vec

    -- problem 4
    namespace matrix 
        -- using the convention that matrix α m n is an m × n matrix
        constant matrix     : Type u → ℕ → ℕ → Type u 

        constant matrix_add     : Π {m n : ℕ}, matrix ℕ m n → matrix ℕ m n → matrix ℕ m n
        constant matrix_mul     : Π {k m n : ℕ}, matrix ℕ k m → matrix ℕ m n → matrix ℕ k n
        constant matrix_vec_mul : Π {m n : ℕ}, matrix ℕ m n → vec.vec ℕ n → vec.vec ℕ m 

        -- some example checks
        constant M : matrix ℕ 3 4 
        constant N : matrix ℕ 3 4
        constant K : matrix ℕ 5 3
        constant v : vec.vec ℕ 4
        #check matrix_add M N 
        #check matrix_mul K M 
        #check matrix_vec_mul M v

    end matrix 


-- ch3
open classical 

variables p q r s : Prop

theorem t1 : p ∧ q ↔ q ∧ p := 
iff.intro 
    (assume h : p ∧ q,
    have hp : p, from h.left,
    have hq : q, from h.right,
    show q ∧ p, from and.intro hq hp)
    (assume h : q ∧ p, 
    have hq : q, from h.left,
    have hp : p, from h.right,
    show p ∧ q, from and.intro hp hq)

example : (p → (q → r)) ↔ (p ∧ q → r) := 
iff.intro 
    (assume h1 : p → (q → r),
    show p ∧ q → r, from
        (assume h2 : p ∧ q,
        have hp : p, from h2.left,
        have hq : q, from h2.right,
        have hr : r, from h1 hp hq,
        show r, from hr)
    )
    (assume h1 : p ∧ q → r,
    show p → (q → r), from (
        assume hp : p, 
        show q → r, from (
            assume hq : q,
            have h2 : p ∧ q, from and.intro hp hq,
            show r, from h1 h2
        )
    )
    )

-- using classical logic
example : ¬(p ↔ ¬p) :=
not.intro 
    (assume h : p ↔ ¬p,
    have h1 : p → ¬p, from iff.mp h,
    have h2 : ¬p → p, from iff.mpr h,
    show false, from or.elim (em p)
        (assume hp : p, 
        show false, from h1 hp hp)
        (assume hnp : ¬p,
        show false, from hnp (h2 hnp) )
    )

-- without using classical logic?
example : ¬(p ↔ ¬p) := sorry
-- not.intro 
--     (assume h : p ↔ ¬p,
--     have h1 : p → ¬p, from iff.mp h,
--     have h2 : ¬p → p, from iff.mpr h,
    
--     show false, from 
--     )



-- tactics
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := 
begin
apply and.intro,
exact hp,
apply and.intro,
exact hq,
exact hp
end


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin 
apply iff.intro,
  intro h, 
  apply or.elim (and.right h),
    intro hq, 
    apply or.intro_left,
    apply and.intro,
      exact and.left h,
      exact hq,
    intro hr, 
    apply or.intro_right,
    apply and.intro,
      exact and.left h,
      exact hr,
  
  intro h, 
  apply or.elim h,
    intro h₁,
    apply and.intro,
      exact and.left h₁,
      apply or.intro_left, 
      exact and.right h₁, 
    intro h₂, 
      apply and.intro,
        exact and.left h₂,
        apply or.intro_right, 
        exact and.right h₂,
end


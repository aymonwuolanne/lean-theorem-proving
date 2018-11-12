
-- ch2 exercises 
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








    

    


-- defining the list type


namespace hidden 
universe u

inductive list (α : Type u)
| nil {}: list 
| cons : α → list → list 

open hidden.list  

#check nil 
#check cons 
#check cons 5 (cons 4 (cons 3 nil))

-- if there is only one list, return that list.
-- if there are multiple lists, but the first one is empty concatenate the rest.
-- if the first one is non-empty take out the first element, 
-- then concatenate the tail and the other lists together,
-- adding the head element onto the concatentation. 
def concat {α : Type}  : list (list α) → list α 
| nil := nil 
| (cons nil L) := concat L 
| (cons (cons hd tl) L) := cons hd (concat (cons tl L))

def len {α : Type} : list α → ℕ 
| nil         := 0 
| (cons hd L) := 1 + len L

-- trying some examples of concat and len
def l₁ : list ℕ := cons 3 (cons 2 (cons 1 nil)) 
def l₂ : list ℕ := cons 4 (cons 5 (cons 6 nil))
def l₃ : list ℕ := cons 1 (cons 1 (cons 1 nil)) 
def L : list (list ℕ) := cons l₁ (cons l₂ (cons l₃ nil))

#reduce concat L 
#reduce len L
#reduce len (concat L)


-- a nonempty predicate
def nonempty {α : Type} : list α → Prop
| nil          := false 
| (cons hd tl) := true

-- true iff all elements of the list of lists is nonempty
def contains_nonempty {α : Type} : list (list α) → Prop 
| nil  := true 
| (cons hd tl) := nonempty hd ∧ contains_nonempty tl

theorem concat_nonempty_is_nonempty : ∀ {α : Type} (L : list (list α)), 
nonempty L → contains_nonempty L → nonempty (concat L) := 
begin 
intros α L h₁ h₂, 
cases L with L_head L_tail, 
  have h : false, from h₁,
  contradiction, 
  
  cases L_head with hd tl, 
    have h : false, 
    from and.left h₂, 
    contradiction, 
    
    rw concat,
    apply trivial
end 

end hidden  
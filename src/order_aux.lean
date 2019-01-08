universe u
variables {α : Type u} [decidable_linear_order α] 
variables {p : α → Prop}

instance : decidable_linear_order (subtype p) := {
    le := λ x y, x.val ≤ y.val,
    le_refl := λ x, le_refl x.val, 
    le_trans := λ a b c h₁ h₂, le_trans h₁ h₂,
    le_antisymm := λ a b h₁ h₂, subtype.eq (decidable_linear_order.le_antisymm a.val b.val h₁ h₂),
    le_total := λ a b, le_total a.val b.val,
    decidable_le := λ a b, decidable_linear_order.decidable_le α a.val b.val
}
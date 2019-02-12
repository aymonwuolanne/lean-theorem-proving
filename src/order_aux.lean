import order.basic

universe u
variables {α : Type u} [decidable_linear_order α]
variables {p : α → Prop}

instance : decidable_linear_order (subtype p) := {
    decidable_le := λ a b, decidable_linear_order.decidable_le α a.val b.val,
    .. subtype.linear_order p
}

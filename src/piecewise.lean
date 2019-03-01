import topology.continuity
import topology.algebra.topological_structures
import data.real.basic

noncomputable theory
universes u v
open set

variables {α : Type u} {β : Type v} [topological_space α] [topological_space β]
variables {s: set α} [decidable_pred s]
variables (f : subtype (closure s) → β) (g : subtype (closure (-s)) → β)

@[reducible] def pw : α → β := λ x, if h : x ∈ s then f ⟨ x, subset_closure h ⟩ else g ⟨ x, subset_closure h ⟩

lemma frontier_subset_closure : frontier s ⊆ closure s := λ x hx, hx.left

lemma frontier_subset_closure_compl : frontier s ⊆ closure (-s) :=
  have h : closure s ∩ closure (-s) = frontier s,
    from symm frontier_eq_closure_inter_closure,
  h ▸ inter_subset_right (closure s) (closure (-s))

local notation `val` := @subtype.val _

theorem continuous_pw (hs : ∀ x (h : x ∈ frontier s),
  f ⟨x, frontier_subset_closure h⟩ = g ⟨x, frontier_subset_closure_compl h⟩)
  (hf : continuous f) (hg : continuous g) : (continuous (pw f g)) :=
continuous_iff_is_closed.mpr $ assume t ht,
  have h₁ : ∃ t₁, is_closed t₁ ∧ f ⁻¹' t = val (closure s) ⁻¹' t₁,
    from is_closed_induced_iff.mp (continuous_iff_is_closed.mp hf t ht),
  have h₂ : ∃ t₂, is_closed t₂ ∧ g ⁻¹' t = val (closure (-s)) ⁻¹' t₂,
    from is_closed_induced_iff.mp (continuous_iff_is_closed.mp hg t ht),
  exists.elim h₁ $
  assume t₁ ht₁,
  exists.elim h₂ $
  assume t₂ ht₂,
  begin
  have : pw f g ⁻¹' t = (closure s ∩ t₁) ∪ (closure (-s) ∩ t₂),
    apply set.ext,
    intro x,
    have hxt₁ : Π  hxc : x ∈ closure s, (x ∈ t₁ ↔ f ⟨x, hxc⟩ ∈ t),
      intro hxc,
      let x' : subtype (closure s) := ⟨x, hxc⟩,
      have h₁ : x ∈ t₁ ↔ x' ∈ val (closure s) ⁻¹' t₁,
        refl,
      have h₂ : x' ∈ val (closure s) ⁻¹' t₁ ↔ x' ∈ f ⁻¹' t,
        rw [ht₁.right],
      rw [h₁, h₂],
      refl,
    have hxt₂ : Π hxi : x ∈ closure (-s), (x ∈ t₂ ↔ g ⟨x, hxi⟩ ∈ t),
      intro hxi,
      let x' : subtype (closure (-s)) := ⟨x, hxi⟩,
      have h₁ : x ∈ t₂ ↔ x' ∈ val (closure (-s)) ⁻¹' t₂,
        refl,
      have h₂ : x' ∈ val (closure (-s)) ⁻¹' t₂ ↔ x' ∈ g ⁻¹' t,
        rw [ht₂.right],
      rw [h₁, h₂],
      refl,

    have hxf : x ∈ frontier s → (x ∈ pw f g ⁻¹' t ↔ x ∈ (closure s ∩ t₁) ∪ (closure (-s) ∩ t₂)),
      intro hx,
      have hxc : x ∈ closure s, from frontier_subset_closure hx,
      have hxi : x ∈ closure (-s), from frontier_subset_closure_compl hx,
      by_cases x ∈ s; simp [pw, h, hxc, hxi, hs x hx, hxt₁ hxc, hxt₂ hxi, -closure_compl],

    have hxnf : x ∉ frontier s → (x ∈ pw f g ⁻¹' t ↔ x ∈ (closure s ∩ t₁) ∪ (closure (-s) ∩ t₂)),
      intro hf,
      by_cases x ∈ s,
        have hc : x ∈ closure s, from subset_closure h,
        have hnc : x ∉ closure (-s),
          rw [closure_compl],
          simpa [frontier, hc] using hf,
        simp [pw, h, hc, hnc, hxt₁ hc, -closure_compl],

        have hc : x ∈ closure (-s), from subset_closure h,
        have hnc : x ∉ closure s,
          simp [closure_compl] at hc,
          simpa [frontier, hc] using hf,
        simp [pw, h, hc, hnc, hxt₂ hc, -closure_compl],

    exact classical.by_cases hxf hxnf,
  exact by rw [this]; exact is_closed_union
    (is_closed_inter is_closed_closure ht₁.left)
    (is_closed_inter is_closed_closure ht₂.left)
  end


#check continuous_if
-- continuous_if is a corollorary of continuous_pw
theorem continuous_if' {p : α → Prop} {f g : α → β} {h : ∀a, decidable (p a)}
  (hp : ∀a∈frontier {a | p a}, f a = g a) (hf : continuous f) (hg : continuous g) :
  continuous (λa, @ite (p a) (h a) β (f a) (g a)) :=
    continuous_pw (f ∘ subtype.val) (g ∘ subtype.val) hp
      (continuous.comp continuous_induced_dom hf)
      (continuous.comp continuous_induced_dom hg)
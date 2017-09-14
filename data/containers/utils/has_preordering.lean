/- This defines a preorder comparison function for comparing elements, and
the notation of a monotonic search predicate for searching within a ordered set.
 -/
import .ordering

section
open ordering

/--
Extend has_ordering to require the cmp function is consistent with a total
preordering.
-/
class has_preordering (α : Type _) extends has_ordering α :=
(refl : ∀ (a: α), cmp a a = eq)
(le_trans : ∀(a b c : α), cmp a b ≤ eq → cmp b c ≤ eq → cmp a c ≠ gt)
(gt_lt_symm : ∀ (a b : α), cmp a b = gt ↔ cmp b a = lt)

end

namespace has_preordering
section
parameters {α : Type _} [has_preordering α]

open has_ordering
open ordering

theorem eq_symm : ∀ (a b : α), cmp a b = eq → cmp b a = eq :=
begin
  intros a b,
  have h0 := gt_lt_symm a b,
  have h1 := gt_lt_symm b a,
  destruct (cmp a b); destruct (cmp b a); cc,
end

theorem eq_trans : ∀ (a b c : α), cmp a b = eq → cmp b c = eq → cmp a c = eq :=
begin
  intros a b c ab bc,
  have h0 := eq_symm a b,
  have h1 := eq_symm b c,
  have h2 := le_trans c b a,
  have h3 := gt_lt_symm c a,
  have h4 := le_trans a b c,
  have h5 : lt ≤ eq := dec_trivial,
  have h6 : eq ≤ eq := dec_trivial,
  destruct (cmp a c); cc,
end


theorem lt_of_lt_of_lt : ∀(a b c : α), cmp a b = lt → cmp b c = lt → cmp a c = lt :=
begin
  intros a b c ab bc,
  have h0 := eq_symm a c,
  have h1 := le_trans c a b,
  have h2 : eq ≤ eq := dec_trivial,
  have h3 : lt ≤ eq := dec_trivial,
  have h4 := gt_lt_symm c b,
  have h5 := le_trans a b c,
  destruct (cmp a c); cc,
end

theorem lt_of_lt_of_eq : ∀(a b c : α), cmp a b = lt → cmp b c = eq → cmp a c = lt :=
begin
  intros a b c,
  have h0 := gt_lt_symm b a,
  have h1 := eq_symm a c,
  have h2 := le_trans b c a,
  have h3 := le_trans a b c,
  have h4 : lt ≤ eq := dec_trivial,
  have h5 : eq ≤ eq := dec_trivial,
  destruct (cmp a c); cc,
end

theorem lt_of_eq_of_lt : ∀(a b c : α), cmp a b = eq → cmp b c = lt → cmp a c = lt :=
begin
  intros a b c,
  have h0 := gt_lt_symm a c,
  have h1 := gt_lt_symm c b,
  have h2 := eq_symm a c,
  have h3 := le_trans c a b,
  have h4 : lt ≤ eq := dec_trivial,
  have h5 : eq ≤ eq := dec_trivial,
  destruct (cmp a c); try { cc },
end

theorem swap_cmp (x y : α)
: (has_ordering.cmp x y).swap = has_ordering.cmp y x :=
begin
  have gt_lt := (gt_lt_symm y x),
  have eq_eq := (eq_symm x y),
  have lt_gt := (gt_lt_symm x y),
  destruct (has_ordering.cmp x y);
  intros d0;
  simp only [d0, ordering.swap];
  cc,
end

end
end has_preordering

-----------------------------------------------------------------------
-- monotonic_find

section
open ordering

/-- This is a search procedure which given an element returns whether
the element is less than, equal to, or greater than the value being searched for.

Note that these axioms will imply that `cmp x = ordering.eq` and `cmp y = ordering.eq`
implies `has_ordering.cmp x y`.
-/
class monotonic_find {E: Type _} [has_preordering E] (cmp : E → ordering) :=
(gt_increases : ∀(x y : E), has_ordering.cmp x y = gt → eq ≤ cmp y → cmp x = gt)
(eq_preserves : ∀(x y : E), has_ordering.cmp x y = eq → cmp x = cmp y)
(lt_decreases : ∀(x y : E), has_ordering.cmp x y = lt → cmp y ≤ eq → cmp x = lt)

end

namespace monotonic_find

/-- This is used to search for an element equivalent to a given element.-/
def eq {α : Type _} [has_preordering α] (e y : α) : ordering := has_ordering.cmp y e

instance eq_is_cmp {α : Type _} [has_preordering α] (e : α) : monotonic_find (eq e) :=
{ gt_increases :=
  begin
    unfold eq,
    intros x y x_gt_y e_ge_y,
    have h0 : ¬ (ordering.eq ≤ ordering.lt) := dec_trivial,
    have h1 := has_preordering.eq_symm y e,
    have h2 := has_preordering.gt_lt_symm x y,
    have h3 := has_preordering.gt_lt_symm x e,
    have h4 := has_preordering.gt_lt_symm y e,
    have h5 := has_preordering.lt_of_eq_of_lt e y x,
    have h6 := has_preordering.lt_of_lt_of_lt e y x,
    destruct has_ordering.cmp y e; intros cmp_y_e; cc,
  end
, eq_preserves :=
  begin
    unfold eq,
    intros x y x_eq_y,
    have h0 := has_preordering.eq_symm x y,
    have h1 := has_preordering.gt_lt_symm x e,
    have h2 := has_preordering.gt_lt_symm y e,
    have h3 := has_preordering.lt_of_eq_of_lt y x e,
    have h4 := has_preordering.eq_trans y x e,
    have h5 := has_preordering.lt_of_lt_of_eq e x y,
    destruct has_ordering.cmp x e; intro cmp_x_e; cc,
  end
, lt_decreases :=
  begin
    unfold eq,
    intros x y x_lt_y y_le_e,
    have h0 : ¬ (ordering.gt ≤ ordering.eq) := dec_trivial,
    have h1 := has_preordering.lt_of_lt_of_lt x y e,
    have h2 := has_preordering.lt_of_lt_of_eq x y e,
    destruct has_ordering.cmp y e; intros cmp_y_e; cc,
  end
}

end monotonic_find

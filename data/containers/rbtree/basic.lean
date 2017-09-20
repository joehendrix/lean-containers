/- This defines a set of elements implemented using a bianry tree. -/
import ..utils.list
import ..utils.has_preordering

universe variable u

namespace data.containers

inductive color
| red : color
| black : color

namespace color

instance : decidable_eq color := by tactic.mk_dec_eq_instance

end color

open color

/-- A red-black tree with no constraints enforced -/
inductive rbtree (E : Type _)
| empty {} : rbtree
| bin : color → rbtree → E → rbtree → rbtree

namespace rbtree

section
parameters {E : Type _}

protected
def tree_color : rbtree E → color
| empty := black
| (bin c l x r) := c

/-- Mark a tree color as black if not already. -/
def set_black : rbtree E → rbtree E
| empty := empty
| (bin c l x r) := bin black l x r

@[simp]
def set_black_is_black (t : rbtree E) : tree_color (set_black t) = black :=
begin
  cases t; simp [set_black, rbtree.tree_color],
end


/-- Create a tree with a single element. -/
def singleton (x : E) : rbtree E := bin black empty x empty

/-- Perform an in-order traversal to return the underlying list. -/
def to_list : rbtree E → list E
| empty := []
| (bin _ l x r) := l.to_list ++ x :: r.to_list

@[simp]
theorem to_list_set_black (t : rbtree E) : (set_black t).to_list = t.to_list :=
begin
  cases t; simp [set_black, to_list],
end


-----------------------------------------------------------------------
-- all_lt

section ordered

parameters [has_preordering E]

/- Return true if keys on right spine of rbtree are less then k. -/
def all_lt : rbtree E → E → Prop
| empty high := true
| (bin _ l x r) high := has_ordering.cmp x high = ordering.lt ∧ all_lt r high

instance all_lt.decidable : ∀(t:rbtree E) (x: E), decidable (all_lt t x)
| empty y := decidable.is_true true.intro
| (bin _ l x r) y := @and.decidable _ _ (by apply_instance) (all_lt.decidable r y)

theorem all_lt_congr
: ∀(t : rbtree E) (y0 y1 : E),
  all_lt t y0
→ has_ordering.cmp y0 y1 ≤ ordering.eq
→ all_lt t y1 :=
begin
  intros t y0 y1,
  induction t,
  case empty { simp [all_lt], },
  case bin _ l x r l_ind r_ind {
    simp [all_lt],

    have h0 := has_preordering.lt_of_lt_of_lt x y0 y1,
    have h1 := has_preordering.lt_of_lt_of_eq x y0 y1,
    have h2 : ¬ (ordering.gt ≤ ordering.eq) := dec_trivial,

    revert l_ind r_ind,
    destruct has_ordering.cmp y0 y1;
    destruct has_ordering.cmp x y0;
    destruct has_ordering.cmp x y1;
    intros def0 def1 def2;
    all_goals { cc, },
  },
end

@[simp]
theorem all_lt_set_black (t : rbtree E) (y : E)
: all_lt (set_black t) y = all_lt t y :=
begin
  cases t; trivial,
end

-----------------------------------------------------------------------
-- all_gt

/- Return true if keys on left spine of rbtree are greater then k. -/
def all_gt : rbtree E → E → Prop
| empty y := true
| (bin _ l x r) y := all_gt l y ∧ has_ordering.cmp y x = ordering.lt

instance all_gt.decidable : ∀(t:rbtree E) (y: E), decidable (all_gt t y)
| empty y := decidable.is_true true.intro
| (bin _ l x r) y := @and.decidable _ _ (all_gt.decidable l y) (by apply_instance)

theorem all_gt_congr
: ∀(t : rbtree E) (y0 y1 : E),
  all_gt t y1
→ has_ordering.cmp y0 y1 ≤ ordering.eq
→ all_gt t y0 :=
begin
  intros t y0 y1,
  induction t,
  case empty { simp [all_gt], },
  case bin _ l x r l_ind r_ind {
    simp [all_gt],

    have h0 := has_preordering.lt_of_lt_of_lt y0 y1 x,
    have h1 := has_preordering.lt_of_eq_of_lt y0 y1 x,
    have h2 : ¬ (ordering.gt ≤ ordering.eq) := dec_trivial,

    revert l_ind r_ind h0 h1,
    cases has_ordering.cmp y0 y1;
    cases has_ordering.cmp y1 x;
    cases has_ordering.cmp y0 x;
    all_goals { cc, },

  },
end


-----------------------------------------------------------------------
-- is_ordered

def is_ordered : rbtree E → Prop
| empty := true
| (bin _ l x r) := is_ordered l ∧ all_lt l x ∧ all_gt r x ∧ is_ordered r

instance is_ordered.decidable : decidable_pred is_ordered
| empty := begin unfold is_ordered, apply_instance, end
| (bin _ l x r) :=
  begin
    unfold is_ordered,
    apply @and.decidable _ _ _ _, exact (is_ordered.decidable l),
    apply @and.decidable _ _ _ _, apply_instance,
    apply @and.decidable _ _ _ _, apply_instance,
    exact (is_ordered.decidable r),
  end

@[simp]
theorem is_ordered_set_black (t : rbtree E)
: is_ordered (set_black t) = is_ordered t :=
begin
  cases t; trivial,
end

end ordered

-----------------------------------------------------------------------
-- well_formed

section well_formed

/-- Returns the height of the black nodes in the tree along the left-most path.-/
def black_height : rbtree E → ℕ
| empty := 0
| (bin black l x r) := l.black_height + 1
| (bin red   l x r) := l.black_height

/--
Returns true if the tree respects the red-black rules, namely:

1. The number of black nodes along every path is the same.
2. The children of a red node must be black.

We omit the rule that the root is black.
-/
def well_formed : rbtree E → Prop
| empty := true
| (bin black l x r) := well_formed l ∧ well_formed r ∧ l.black_height = r.black_height
| (bin red l x r)
  := l.tree_color = black
   ∧ r.tree_color = black
   ∧ well_formed l ∧ well_formed r ∧ l.black_height = r.black_height

instance well_formed.decidable : decidable_pred well_formed
| empty := begin unfold well_formed, apply_instance end
| (bin black l x r) :=
  begin
    unfold well_formed,
    apply @and.decidable _ _ _ _, exact (well_formed.decidable l),
    apply @and.decidable _ _ _ _, exact (well_formed.decidable r),
    apply_instance,
  end
| (bin red l x r) :=
  begin
    unfold well_formed,
    apply @and.decidable _ _ _ _, apply_instance,
    apply @and.decidable _ _ _ _, apply_instance,
    apply @and.decidable _ _ _ _, exact (well_formed.decidable l),
    apply @and.decidable _ _ _ _, exact (well_formed.decidable r),
    apply_instance,
  end

end well_formed

-----------------------------------------------------------------------
-- lookup

section lookup
parameters [has_preordering E]
parameters (p : E → ordering) [monotonic_find p]

/-- Lookup an element that matches the ordering. -/
def lookup : rbtree E → option E
| empty := none
| (bin _ l x r) :=
  match p x with
  | ordering.lt := lookup r
  | ordering.eq := x
  | ordering.gt := lookup l
  end

theorem find_eq_is_none_of_all_gt {t : rbtree E} {y : E}
: is_ordered t
→ all_gt t y
→ p y = ordering.gt
→ list.find (eq ordering.eq ∘ p) (to_list t) = failure :=
begin
  induction t,
  case empty { intros, trivial, },
  case bin _ l x r ind_l ind_r {
    have h0 : ordering.eq ≠ ordering.gt := dec_trivial,
    have h4 : (eq ordering.eq ∘ p) x = (ordering.eq = p x) := by simp [function.comp],

    simp [is_ordered, all_gt, to_list],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_gt_l_y y_lt_x p_y_gt,
    have p_x_gt : p x = ordering.gt :=
       monotonic_find.gt_increases x y (by simp [has_preordering.gt_lt_symm, y_lt_x])
                                         (by simp [p_y_gt]),
    have all_gt_r_y : all_gt r y :=
       all_gt_congr r y x all_gt_r_x (begin simp [y_lt_x], end),
    simp [*, list.find_append, list.find_cons, option.failure_is_none, option.none_or_else],
  },
end

theorem find_eq_is_none_of_all_lt {t : rbtree E} {y : E}
: is_ordered t
→ all_lt t y
→ p y ≤ ordering.eq
→ list.find (eq ordering.eq ∘ p) (to_list t) = failure :=
begin
  induction t,
  case empty { intros, trivial, },
  case bin _ l x r ind_l ind_r {
    have h0 : ordering.eq ≠ ordering.lt := dec_trivial,
    have h4 : (eq ordering.eq ∘ p) x = (ordering.eq = p x) := by simp [function.comp],

    simp [is_ordered, all_lt, to_list],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_gt_r_y x_lt_y p_y_gt,
    have p_x_lt : p x = ordering.lt := monotonic_find.lt_decreases x y x_lt_y  (begin simp[p_y_gt] end),
    have all_lt_l_y : all_lt l y, apply all_lt_congr l x y all_lt_l_x (begin simp [x_lt_y], end),
    simp [*, list.find_append, list.find_cons, option.failure_is_none, option.or_else_none],
  },
end

theorem lookup_as_list
: ∀{t : rbtree E},
   is_ordered t
   → lookup t = t.to_list.find (eq ordering.eq ∘ p) :=
begin
  intros t,
  induction t,
  case rbtree.empty { intro is_ordered_t, refl, },
  case rbtree.bin _ l x r l_ind r_ind {
    have h0 : ordering.eq ≠ ordering.lt := dec_trivial,
    have h1 : ordering.eq ≠ ordering.gt := dec_trivial,
    have h2 : ordering.lt ≤ ordering.eq := dec_trivial,
    have h3 : ordering.eq ≤ ordering.gt := dec_trivial,
    have h4 : (eq ordering.eq ∘ p) x = (ordering.eq = p x) := by simp [function.comp],

    simp [lookup, to_list, is_ordered],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x,
    have find_l_is_none := find_eq_is_none_of_all_lt p is_ordered_l all_lt_l_x,
    have find_r_is_none := find_eq_is_none_of_all_gt p is_ordered_r all_gt_r_x,
    destruct (p x);
      intro px_def;
      simp [px_def, h1] at find_l_is_none find_r_is_none;
      simp [lookup, *, list.find_append, list.find_cons,
            option.coe_is_some,
            option.failure_is_none,
            option.none_or_else,
             option.or_else_none],
  },
end

theorem lookup_eq_of_to_list_eq
: ∀{t u : rbtree E},
   is_ordered t
   → is_ordered u
   → t.to_list = u.to_list
   → lookup t = lookup u :=
begin
  intros x y x_order y_order x_eq_y,
  simp [lookup_as_list p, *],
end

end lookup


parameters [has_preordering E]

def key_is_lt (y : E) (p : E) : Prop := has_ordering.cmp p y = ordering.lt

instance key_is_lt_decidable (y : E) : decidable_pred (key_is_lt y) :=
  begin dsimp [decidable_pred, key_is_lt], apply_instance, end

def key_is_gt (y : E) (p : E) : Prop := has_ordering.cmp y p = ordering.lt

instance key_is_gt_decidable (y : E) : decidable_pred (key_is_gt y) :=
  begin dsimp [decidable_pred, key_is_gt], apply_instance, end

theorem filter_lt_of_all_lt (t : rbtree E) (y : E)
: is_ordered t → all_lt t y → t.to_list.filter (key_is_lt y) = t.to_list :=
begin
  induction t,
  case empty { intros, refl, },
  case bin _ l x r l_ind r_ind {
    simp [is_ordered, all_lt, to_list, list.filter, key_is_lt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_r_y cmp_lt,
    have all_lt_ly := all_lt_congr l x y all_lt_l_x (by simp [cmp_lt]),
    simp [*],
  },
end

theorem filter_gt_of_all_lt (t : rbtree E) (y : E)
: is_ordered t → all_lt t y → t.to_list.filter (key_is_gt y) = [] :=
begin
  induction t,
  case empty { intros, refl, },
  case bin _ l x r l_ind r_ind {
    simp [is_ordered, all_lt, to_list, list.filter, key_is_gt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_r_y cmp_lt,
    have all_lt_ly := all_lt_congr l x y all_lt_l_x (by simp [cmp_lt]),
    have h : has_ordering.cmp y x ≠ ordering.lt, {
      rw [← has_preordering.swap_cmp x y, cmp_lt],
      trivial,
    },
    simp [*],
  },
end

 theorem filter_gt_of_all_gt (t : rbtree E) (y : E)
: is_ordered t → all_gt t y → t.to_list.filter (key_is_gt y) = t.to_list :=
begin
  induction t,
  case empty { intros, refl, },
  case bin _ l x r l_ind r_ind {
    simp [is_ordered, all_gt, to_list, list.filter, key_is_gt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_l_y cmp_lt,
    have all_gt_ry := all_gt_congr r y x all_gt_r_x (by simp [cmp_lt]),
    simp [*],
  },
end

theorem filter_lt_of_all_gt (t : rbtree E) (y : E)
: is_ordered t → all_gt t y →  list.filter (key_is_lt y) (to_list t) = [] :=
begin
  induction t,
  case empty { intros, refl, },
  case bin _ l x r l_ind r_ind {
    simp [is_ordered, all_gt, to_list, list.filter, key_is_lt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_l_y cmp_lt,
    have all_gt_ry := all_gt_congr r y x all_gt_r_x (by simp [cmp_lt]),
    have h : has_ordering.cmp x y ≠ ordering.lt, {
      rw [← has_preordering.swap_cmp y x, cmp_lt],
      trivial,
    },
    simp [*],
  },
end

end
end rbtree
end data.containers
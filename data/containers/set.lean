/- This defines a set of elements implemented using a bianry tree. -/
import .utils.list
import .utils.has_preordering

universe variable u

namespace data.containers

inductive bintree (E : Type _)
| empty {} : bintree
| bin : bintree → E → bintree → bintree

namespace bintree
section
parameters {E : Type _}

def to_list : bintree E → list E
| empty := []
| (bin l x r) := l.to_list ++ x :: r.to_list

end

section

parameters {E : Type _}
parameters [has_preordering E]

/-- Create a tree with a single element. -/
def singleton (x : E) : bintree E := bin empty x empty

-----------------------------------------------------------------------
-- all_lt

/- Return true if keys on right spine of bintree are less then k. -/
def all_lt : bintree E → E → Prop
| empty high := true
| (bin l x r) high := has_ordering.cmp x high = ordering.lt ∧ all_lt r high

instance all_lt.decidable : ∀(t:bintree E) (x: E), decidable (all_lt t x)
| empty y := begin unfold all_lt, apply_instance, end
| (bin l x r) y :=
  begin
    unfold all_lt,
    exact @and.decidable _ _ (by apply_instance) (all_lt.decidable r y),
  end

theorem all_lt_congr
: ∀(t : bintree E) (y0 y1 : E),
  all_lt t y0
→ has_ordering.cmp y0 y1 ≤ ordering.eq
→ all_lt t y1 :=
begin
  intros t y0 y1,
  induction t,
  case empty { simp [all_lt], },
  case bin l x r l_ind r_ind {
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

-----------------------------------------------------------------------
-- all_gt

/- Return true if keys on left spine of bintree are greater then k. -/
def all_gt : bintree E → E → Prop
| empty y := true
| (bin l x r) y := all_gt l y ∧ has_ordering.cmp y x = ordering.lt

instance all_gt.decidable : ∀(t:bintree E) (y: E), decidable (all_gt t y)
| empty y := begin unfold all_gt, apply_instance, end
| (bin l x r) y :=
  begin
    unfold all_gt,
    exact @and.decidable _ _ (all_gt.decidable l y) (by apply_instance),
  end

theorem all_gt_congr
: ∀(t : bintree E) (y0 y1 : E),
  all_gt t y1
→ has_ordering.cmp y0 y1 ≤ ordering.eq
→ all_gt t y0 :=
begin
  intros t y0 y1,
  induction t,
  case empty { simp [all_gt], },
  case bin l x r l_ind r_ind {
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

def is_ordered : bintree E → Prop
| empty := true
| (bin l x r) := is_ordered l ∧ all_lt l x ∧ all_gt r x ∧ is_ordered r

instance is_ordered.decidable : decidable_pred is_ordered
| empty := begin unfold is_ordered, apply_instance, end
| (bin l x r) :=
  begin
    unfold is_ordered,
    apply @and.decidable _ _ _ _, exact (is_ordered.decidable l),
    apply @and.decidable _ _ _ _, apply_instance,
    apply @and.decidable _ _ _ _, apply_instance,
    exact (is_ordered.decidable r),
  end

-----------------------------------------------------------------------
-- lookup

section lookup

parameters (p : E → ordering) [monotonic_find p]

/-- Lookup an element that matches the ordering. -/
def lookup : bintree E → option E
| empty := none
| (bin l x r) :=
  match p x with
  | ordering.lt := lookup r
  | ordering.eq := x
  | ordering.gt := lookup l
  end


theorem find_eq_is_none_of_all_gt {t : bintree E} {y : E}
: is_ordered t
→ all_gt t y
→ p y = ordering.gt
→ list.find (eq ordering.eq ∘ p) (to_list t) = failure :=
begin
  induction t,
  case empty { intros, trivial, },
  case bin l x r ind_l ind_r {
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

theorem find_eq_is_none_of_all_lt {t : bintree E} {y : E}
: is_ordered t
→ all_lt t y
→ p y ≤ ordering.eq
→ list.find (eq ordering.eq ∘ p) (to_list t) = failure :=
begin
  induction t,
  case empty { intros, trivial, },
  case bin l x r ind_l ind_r {
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
: ∀{t : bintree E},
   is_ordered t
   → lookup t = t.to_list.find (eq ordering.eq ∘ p) :=
begin
  intros t,
  induction t,
  case bintree.empty { intro is_ordered_t, refl, },
  case bintree.bin l x r l_ind r_ind {
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
: ∀{t u : bintree E},
   is_ordered t
   → is_ordered u
   → t.to_list = u.to_list
   → lookup t = lookup u :=
begin
  intros x y x_order y_order x_eq_y,
  simp [lookup_as_list p, *],
end

end lookup

-----------------------------------------------------------------------
-- insert

def insert (y : E) : bintree E → bintree E
| empty := singleton y
| (bin l x r) :=
  match has_ordering.cmp y x with
  | ordering.lt := bin (insert l) x r
  | ordering.eq := bin l y r
  | ordering.gt := bin l x (insert r)
  end

/-- Prove inserting into a smaller tree is still smaller. -/
def all_lt_insert (y : E) (t : bintree E) (bnd : E)
  (key_lt_u : has_ordering.cmp y bnd = ordering.lt)
  (pre : all_lt t bnd)
: all_lt (insert y t) bnd :=
begin
  induction t,
  case empty {
    simp [insert, singleton, all_lt, *],
  },
  case bin l x r l_ind r_ind {
    simp only [all_lt] at pre,
    simp only [insert],
    cases (has_ordering.cmp y x); simp only [insert, all_lt]; cc,
  },
end

def all_gt_insert (y : E) (t : bintree E) (bnd : E)
  (key_lt_u : has_ordering.cmp bnd y = ordering.lt)
  (pre : all_gt t bnd)
: all_gt (insert y t) bnd :=
begin
  induction t,
  case empty {
    simp [insert, singleton, all_gt, *],
  },
  case bin l x r l_ind r_ind {
    simp only [all_gt] at pre,
    simp only [insert],
    cases (has_ordering.cmp y x); simp only [insert, all_gt]; cc,
  },
end

theorem is_ordered_insert (y : E) (t : bintree E)
: is_ordered t → is_ordered (insert y t) :=
begin
  induction t,
  case empty {
    simp [insert, singleton, is_ordered, all_gt, all_lt],
  },
  case bin l x r l_ind r_ind {
    simp only [is_ordered, insert],
    intro props,
    cases props with l_ordered props,
    cases props with all_lt_l props,
    cases props with all_gt_r r_ordered,
    destruct (has_ordering.cmp y x); intro ordering_eq; simp [ordering_eq, insert, is_ordered, *],
    { apply all_lt_insert; cc, },
    { have k_key_eq := has_preordering.eq_symm _ _ ordering_eq,
      have h_lt := all_lt_congr l x y,
      simp [k_key_eq, le_refl] at h_lt,
      have h_gt:= all_gt_congr r y x,
      simp [ordering_eq, le_refl] at h_gt,
      simp [*],
    },
    { simp only [has_preordering.gt_lt_symm] at ordering_eq,
      apply all_gt_insert; cc,
    },
  }
end

def key_is_lt (y : E) (p : E) : Prop := has_ordering.cmp p y = ordering.lt

instance key_is_lt_decidable (y : E) : decidable_pred (key_is_lt y) :=
  begin dsimp [decidable_pred, key_is_lt], apply_instance, end

def key_is_gt (y : E) (p : E) : Prop := has_ordering.cmp y p = ordering.lt

instance key_is_gt_decidable (y : E) : decidable_pred (key_is_gt y) :=
  begin dsimp [decidable_pred, key_is_gt], apply_instance, end

theorem filter_lt_of_all_lt (t : bintree E) (y : E)
: is_ordered t → all_lt t y → t.to_list.filter (key_is_lt y) = t.to_list :=
begin
  induction t,
  case empty { intros, refl, },
  case bin l x r l_ind r_ind {
    simp [is_ordered, all_lt, to_list, list.filter, key_is_lt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_r_y cmp_lt,
    have all_lt_ly := all_lt_congr l x y all_lt_l_x (by simp [cmp_lt]),
    simp [*],
  },
end

theorem filter_gt_of_all_lt (t : bintree E) (y : E)
: is_ordered t → all_lt t y → t.to_list.filter (key_is_gt y) = [] :=
begin
  induction t,
  case empty { intros, refl, },
  case bin l x r l_ind r_ind {
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

 theorem filter_gt_of_all_gt (t : bintree E) (y : E)
: is_ordered t → all_gt t y → t.to_list.filter (key_is_gt y) = t.to_list :=
begin
  induction t,
  case empty { intros, refl, },
  case bin l x r l_ind r_ind {
    simp [is_ordered, all_gt, to_list, list.filter, key_is_gt],
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x all_lt_l_y cmp_lt,
    have all_gt_ry := all_gt_congr r y x all_gt_r_x (by simp [cmp_lt]),
    simp [*],
  },
end

theorem filter_lt_of_all_gt (t : bintree E) (y : E)
: is_ordered t → all_gt t y →  list.filter (key_is_lt y) (to_list t) = [] :=
begin
  induction t,
  case empty { intros, refl, },
  case bin l x r l_ind r_ind {
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


theorem to_list_insert (y : E) (t : bintree E)
: is_ordered t → to_list (insert y t)
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  induction t,
  case empty {
    simp [insert, singleton, to_list],
  },
  case bin l x r l_ind r_ind {
    simp [insert, to_list, is_ordered, list.filter, key_is_lt, key_is_gt],

    have g1 : (ordering.gt ≠ ordering.lt), exact dec_trivial,
    have g2 : ordering.lt ≤ ordering.eq, exact dec_trivial,
    have g3 : ordering.eq ≤ ordering.eq, exact dec_trivial,
    have g4 : ordering.eq ≠ ordering.lt, exact dec_trivial,

    have cmp_k_key_eq : has_ordering.cmp x y = (has_ordering.cmp y x).swap,
    { rw [has_preordering.swap_cmp], },

    have all_lt_r_key := all_lt_congr l x y,
    have all_gt_r_key := all_gt_congr r y x,
    have l_lt := filter_lt_of_all_lt l y,
    have l_gt := filter_gt_of_all_lt l y,
    have r_lt := filter_lt_of_all_gt r y,
    have r_gt := filter_gt_of_all_gt r y,
    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x,
    revert all_lt_r_key all_gt_r_key l_lt l_gt r_lt r_gt,

    destruct (has_ordering.cmp y x);
      intros cmp_key_k;
      simp only [cmp_key_k];
      simp [cmp_key_k, ordering.swap] at cmp_k_key_eq;
      intros all_lt_r_key all_gt_r_key l_lt l_gt r_lt r_gt;
      simp [*, insert, to_list],
  },
end

end

theorem insert_eq {E : Type _} [has_preordering E] (y : E)
: ∀{t u : bintree E},
   is_ordered t
   → is_ordered u
   → t.to_list = u.to_list
   → to_list (insert y t) = to_list (insert y t) :=
begin
  intros x y x_order y_order x_eq_y,
  simp [to_list_insert, *],
end

end bintree

-----------------------------------------------------------------------
-- ordered_tree

structure ordered_tree (E : Type _) [has_preordering E] :=
(tree : bintree E)
(ordered : bintree.is_ordered tree)

namespace ordered_tree

section
parameters {E : Type _} [has_preordering E]

def empty : ordered_tree E :=
{ tree := bintree.empty
, ordered := dec_trivial
}

def singleton (x : E) : ordered_tree E :=
{ tree := bintree.singleton x
, ordered := dec_trivial
}

def to_list (x : ordered_tree E) : list E := x.tree.to_list

section lookup
parameters (p : E → ordering) [monotonic_find p]


def lookup (t : ordered_tree E) : option E := t.tree.lookup p

theorem lookup_eq_of_to_list_eq
: ∀{t u : ordered_tree E},
   t.to_list = u.to_list
   → lookup t = lookup u :=
begin
  intros t u t_eq_u,
  have t1 := t.ordered,
  have u1 := u.ordered,
  simp [to_list] at t_eq_u,
  simp [lookup],
  apply bintree.lookup_eq_of_to_list_eq; assumption,
end

end lookup

def insert (y : E) (t : ordered_tree E) : ordered_tree E :=
{ tree := bintree.insert y t.tree
, ordered :=
  begin
    apply bintree.is_ordered_insert _ _ t.ordered,
  end
}

theorem insert_eq (y : E)
: ∀{t u : ordered_tree E},
   t.to_list = u.to_list
   → to_list (insert y t) = to_list (insert y u) :=
begin
  intros t u,
  unfold insert to_list,
  intros t_eq_u,
  simp [bintree.to_list_insert y t.tree t.ordered, bintree.to_list_insert y u.tree u.ordered, *],
end

end

/-- Equivalence relation that equates two trees if underlying lists are equal. -/
def to_list_equal {E : Type _} [has_preordering E]
       (x y : ordered_tree E) : Prop := x.to_list = y.to_list

namespace to_list_equal
section
parameters (E : Type _) [inst : has_preordering E]

def refl : reflexive (@to_list_equal E inst) :=
begin intro x, unfold to_list_equal, end

def symm : symmetric (@to_list_equal E inst) :=
begin intros x y, apply eq.symm, end

def trans : transitive (@to_list_equal E inst) :=
begin intros x y z, apply eq.trans, end

def equiv : equivalence (@to_list_equal E inst) :=
mk_equivalence to_list_equal refl symm trans

end
end to_list_equal

instance to_list_equal_is_decidable {E : Type _} [has_preordering E] [decidable_eq E]
   (t u : ordered_tree E) : decidable (to_list_equal t u) :=
begin
  unfold to_list_equal,
  apply_instance,
end

instance is_setoid (E : Type _) [has_preordering E]
: setoid (ordered_tree E) :=
{ r := to_list_equal
, iseqv := to_list_equal.equiv _
}

end ordered_tree

-----------------------------------------------------------------------
-- set

/-- A set of elements. -/
def set (E : Type _) [has_preordering E] := quotient (ordered_tree.is_setoid E)

namespace set

section
parameters {E : Type _} [has_preordering E]

protected def from_tree (t : ordered_tree E) : set E := quotient.mk t

/-- Create the empty set. -/
def empty : set E := from_tree ordered_tree.empty

/-- Create a set with a single element. -/
def singleton (x : E) : set E := from_tree (ordered_tree.singleton x)

/-- Insert an element into a set. -/
def insert (y : E) (m : set E) : set E :=
  let insert_each (t:ordered_tree E) := from_tree (ordered_tree.insert y t) in
  let pr (t u : ordered_tree E) (bin_eq : t ≈ u) : insert_each t = insert_each u :=
        quotient.sound (ordered_tree.insert_eq y bin_eq) in
  quotient.lift insert_each pr m

/-- Lookup an element `x` in the set for which `p x = ordering.eq`. -/
def lookup (p : E → ordering) [inst : monotonic_find p] : set E → option E :=
  quotient.lift (ordered_tree.lookup p) (λx y, ordered_tree.lookup_eq_of_to_list_eq p)

instance : has_mem E (set E) :=
{ mem := λy t, option.is_some (lookup (monotonic_find.eq y) t) = tt
}

/-- Return the ordered list of elements in the set. -/
def to_list : set E → list E :=
  quotient.lift ordered_tree.to_list (λt u, id)

instance [decidable_eq E] : decidable_eq (set E) := by apply_instance

end
end set

end data.containers
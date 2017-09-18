import .basic

namespace data.containers
namespace rbtree

open color

/-- An insert_result is a generalization of the tree to allow
temporaries tree-like structures that don't respect the red-black rules.

Specifically, it is either a tree that respects the red-black rules,
or a the concatenation of three trees with the same height.
-/
inductive insert_result (E : Type _)
| tree : Π (t : rbtree E), insert_result
-- When inserting into a binary tree that respects the ordering
-- and red-black color rules, by construction we know that the trees
-- are in ascending order, either the first or third tree are colored
-- black, and the center node is colored black.
| triple : rbtree E → E → rbtree E →  E → rbtree E → insert_result

namespace insert_result
section
parameters {E:Type _}

/--
Convert an insert result to a tree.

N.B. This may increase the black-height, so should only be called in contexts
where that matters (i.e. at the roto.)
-/
def as_tree : insert_result E → rbtree E
| (tree u) := u
| (triple l x c y r) :=
  match l with
  | bin red ll lx lr := bin black (bin black ll lx lr) x (bin black c y r)
  | _ := bin black (bin red l x c) y r
  end


def to_list : insert_result E → list E
| (tree t) := t.to_list
| (triple l x c y r) := l.to_list ++ [x] ++ c.to_list ++ [y] ++ r.to_list

parameters [has_preordering E]

/-- Check whether a insert_result respects the ordering relation. -/
def is_ordered : insert_result E → Prop
| (tree t) := t.is_ordered
| (triple l x c y r) :=
   l.is_ordered
   ∧ all_lt l x
   ∧ all_gt c x
   ∧ c.is_ordered ∧ has_ordering.cmp x y = ordering.lt
   ∧ all_lt c y
   ∧ all_gt r y
   ∧ r.is_ordered

instance (r : insert_result E) : decidable (is_ordered r) :=
begin
  cases r; simp [is_ordered]; apply_instance,
end

/- Return true if keys on right spine of rbtree are less then k. -/
def all_lt : insert_result E → E → Prop
| (tree t) a := t.all_lt a
| (triple l x c y r) a :=
  has_ordering.cmp y a = ordering.lt ∧ r.all_lt a

/- Return true if keys on right spine of rbtree are less then k. -/
def all_gt : insert_result E → E → Prop
| (tree t) a := t.all_gt a
| (triple l x c y r) a :=
  has_ordering.cmp a x = ordering.lt ∧ l.all_gt a

end
end insert_result

section
parameters {E:Type _}

section insert_def

open insert_result

def balanceL : color → insert_result E → E → rbtree E → insert_result E
-- In this case, the caller should be able to guarantee that co is black, so the
-- black depth of the tree should not change.
| co (triple ll lx lc ly lr) x r :=
  tree (bin red (bin black ll lx lc) ly (bin black lr x r))
| co (tree l) x r :=
  match (co, l) with
  | (red, bin red ll lx lr) := triple ll lx lr x r
  | _ := tree (bin co l x r)
  end

def balanceR : color → rbtree E → E → insert_result E → insert_result E
-- In this case co is guaranteed to be black, so the
-- black depth of the tree should not change.
| co l x (triple rl rx rc ry rr) :=
  tree (bin red (bin black l x rl) rx (bin black rc ry rr))
| co l x  (tree r) :=
  match (co, r) with
  | (red, bin red rl rx rr) := triple l x rl rx rr
  | _ := tree (bin co l x r)
  end

parameters [has_preordering E]

def insert_core (y : E) : rbtree E → insert_result E
| empty := tree (bin red empty y empty)
| (bin c l x r) :=
  match has_ordering.cmp y x with
  | ordering.lt := balanceL c (insert_core l) x r
  | ordering.eq := tree (bin c l y r)
  | ordering.gt := balanceR c l x (insert_core r)
  end

def insert (y : E) (t : rbtree E) : rbtree E :=
  (insert_core y t).as_tree

end insert_def

-----------------------------------------------------------------------
-- to_list

section to_list_theorems

theorem to_list_balanceL (c : color) (l : insert_result E) (x : E) (r : rbtree E)
: (balanceL c l x r).to_list  = l.to_list ++ [x] ++ r.to_list :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  simp [*, balanceL, insert_result.to_list, to_list],
end

theorem to_list_balanceR
(c : color) (l : rbtree E) (x : E) (r : insert_result E)
: (balanceR c l x r).to_list = l.to_list ++ [x] ++ r.to_list :=
begin
  cases r with t l x tc y r;
    try {
      cases t with rc rl rx rr; try { cases rc };
        cases c,
    };
  simp [*, balanceR, insert_result.to_list, to_list],
end

parameters [has_preordering E]

theorem to_list_insert_core (y : E) (t : rbtree E)
: is_ordered t
→ (insert_core y t).to_list
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  induction t,
  case empty {
    intros,
    simp [insert_core, insert_result.to_list, to_list],
  },
  case bin c l x r l_ind r_ind {
    simp [is_ordered, insert_core, to_list, list.filter, key_is_lt, key_is_gt],

    have g1 : (ordering.gt ≠ ordering.lt), exact dec_trivial,
    have g2 : ordering.lt ≤ ordering.eq, exact dec_trivial,
    have g3 : ordering.eq ≤ ordering.eq, exact dec_trivial,
    have g4 : ordering.eq ≠ ordering.lt, exact dec_trivial,

    have cmp_x_y_eq : has_ordering.cmp x y = (has_ordering.cmp y x).swap,
    { rw [has_preordering.swap_cmp], },

    intros iso_l iso_r all_gt_r_x all_lt_l_x,
    have all_lt_r_key := all_lt_congr l x y,
    have all_gt_r_key := all_gt_congr r y x,
    have l_lt := filter_lt_of_all_lt l y,
    have l_gt := filter_gt_of_all_lt l y,
    have r_lt := filter_lt_of_all_gt r y,
    have r_gt := filter_gt_of_all_gt r y,
    destruct (has_ordering.cmp y x); intro cmp_y_x;
      simp [cmp_y_x, ordering.swap] at cmp_x_y_eq,
    { simp [insert_core, *, to_list_balanceL, l_ind], },
    { simp [insert_core, *, insert_result.to_list, to_list ], },
    { simp [insert_core, *, to_list_balanceR, r_ind], },
  },
end

theorem as_tree_to_list (r : insert_result E)
: r.as_tree.to_list = r.to_list :=
begin
  cases r with t tl tx tc ty tr;
    try { cases tl with tlc tll tlx tlr;  try { cases tlc },
    };
    simp [insert_result.as_tree, rbtree.tree_color, insert_result.to_list, to_list],
end

theorem to_list_insert (y : E) (t : rbtree E) : is_ordered t
 → to_list (insert y t)
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  intros,
  simp [insert, as_tree_to_list, to_list_insert_core, *],
end

theorem insert_eq (y : E)
: ∀{t u : rbtree E},
   is_ordered t
   → is_ordered u
   → t.to_list = u.to_list
   → to_list (insert y t) = to_list (insert y t) :=
begin
  intros x y x_order y_order x_eq_y,
  simp [to_list_insert, *],
end

end to_list_theorems

-----------------------------------------------------------------------
-- is_ordered

section is_ordered_theorems
parameters [has_preordering E]
local attribute [simp] balanceL balanceR insert_result.is_ordered is_ordered
  insert_result.all_lt all_lt insert_result.all_gt all_gt
  insert_core

section balanceL
parameters (c : color) (l : insert_result E) (y : E) (r : rbtree E)

def all_lt_balanceL (a : E)
  (all_lt_l : l.all_lt a)
  (y_lt_bnd : has_ordering.cmp y a = ordering.lt)
  (all_lt_r : all_lt r a)
: (balanceL c l y r).all_lt a :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try { simp at all_lt_l, simp [*], },
end

def all_gt_balanceL (a : E)
  (iso : l.is_ordered)
  (a_lt_y : has_ordering.cmp a y = ordering.lt)
  (all_gt_l : l.all_gt a)
: (balanceL c l y r).all_gt a :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try { simp at all_gt_l, simp [*], },
  simp at iso,
  apply has_preordering.lt_of_lt_of_lt a tx ty; simp [*],
end

def is_ordered_balanceL
  (l_iso : l.is_ordered)
  (all_lt_l_y : l.all_lt y)
  (all_gt_r_y : all_gt r y)
  (iso_r : is_ordered r)
: (balanceL c l y r).is_ordered :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try {   simp at l_iso all_lt_l_y, simp [*],},
end
end balanceL

section balanceR
parameters (c : color) (l : rbtree E) (y : E) (r : insert_result E)

def all_lt_balanceR (a : E)
  (iso : r.is_ordered)
  (y_lt_a : has_ordering.cmp y a = ordering.lt)
  (all_lt_r_a : r.all_lt a)
: (balanceR c l y r).all_lt a :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_lt_r_a, simp [*], },
  simp at iso,
  apply has_preordering.lt_of_lt_of_lt tx ty a; simp [*],
end


def all_gt_balanceR (a : E)
  (a_lt_y : has_ordering.cmp a y = ordering.lt)
  (all_gt_l : all_gt l a)
  (all_gt_r : r.all_gt a)
: (balanceR c l y r).all_gt a :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_gt_r, simp[*], },
end

def is_ordered_balanceR
  (l_iso : is_ordered l)
  (all_lt_l_y : all_lt l y)
  (all_gt_r_y : r.all_gt y)
  (r_iso : r.is_ordered)
: (balanceR c l y r).is_ordered :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_gt_r_y r_iso, simp[*], },
end
end balanceR

def insert_core_preserves (y : E) {t : rbtree E}
  (iso : is_ordered t)
: (insert_core y t).is_ordered
∧ (∀ (a : E), has_ordering.cmp y a = ordering.lt
            → t.all_lt a
            → (insert_core y t).all_lt a)
∧ (∀ (a:E), has_ordering.cmp a y = ordering.lt
               → t.all_gt a
               → (insert_core y t).all_gt a) :=
begin
  induction t,
  case empty {
    intros,
    simp,
  },
  case bin c l x r l_ind r_ind {
    simp at iso,
    simp only [iso, true_implies_iff] at l_ind r_ind,
    have l_all_lt := l_ind.right.left,
    have r_all_gt := r_ind.right.right,
    destruct (has_ordering.cmp y x);
      intro cmp_y_s;
      simp only [cmp_y_s, insert_core, all_lt],
    { apply and.intro,
      { apply is_ordered_balanceL,
        all_goals { simp [*], },
      },
      apply and.intro,
      { intros a y_lt_a pr,
        apply all_lt_balanceL,
        apply l_all_lt,
        all_goals { try { simp [*],} },
        apply all_lt_congr l x a; simp[*],
      },
      { intros a a_lt_y pr,
        simp at pr,
        apply all_gt_balanceL,
        all_goals { simp [*], },
      }
    },
    { apply and.intro,
      { simp [*],
        apply and.intro,
        { apply all_gt_congr r y x; simp [*], },
        { have h0 := has_preordering.eq_symm y x,
          apply all_lt_congr l x y; simp [*],
        },
      },
      apply and.intro,
      { intros a y_lt_a x_lt_a, simp [*], },
      { intros a a_lt_y gt_a, simp at gt_a, simp [*], },
    },
    { rw [has_preordering.gt_lt_symm] at cmp_y_s,
      apply and.intro,
      { apply is_ordered_balanceR; simp[*], },
      apply and.intro,
      { intros a y_lt_a x_lt_a,
        apply all_lt_balanceR; simp[*],
      },
      { intros a a_lt_y pr,
        simp at pr,
        apply all_gt_balanceR; try { simp[*] },
        apply r_all_gt; try {simp[*]},
        apply all_gt_congr r a x; try {simp[*]},
      },
    },
  },
end

def as_tree_insert_result_ordered {r : insert_result E}
  (iso : r.is_ordered)
: r.as_tree.is_ordered :=
begin
  cases r with t tl tx tc ty tr;
    try { cases tl with lc ll lx lr; try { cases lc}, };
  simp at iso; simp [insert_result.as_tree, *],
end

theorem is_ordered_insert (y : E) (t : rbtree E)
: is_ordered t → is_ordered (insert y t) :=
begin
  intro iso,
  simp [insert],
  apply as_tree_insert_result_ordered,
  have h := insert_core_preserves y iso,
  simp[h],
end
end is_ordered_theorems

end
end rbtree
end data.containers
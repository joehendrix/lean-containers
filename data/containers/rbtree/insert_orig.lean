import .basic

namespace data.containers
namespace rbtree
section insert

parameters {E:Type _}
open color

-----------------------------------------------------------------------
-- defs.

section insert

def balanceL : color → rbtree E → E → rbtree E → rbtree E
| black (bin red (bin red lll llx llr) lx lr) x r := bin red (bin black lll llx llr) lx (bin black lr x r)
| black (bin red ll lx (bin red lrl lrx lrr)) x r := bin red (bin black ll lx lrl) lrx (bin black lrr x r)
| c l x r := bin c l x r

def balanceR : color → rbtree E → E → rbtree E → rbtree E
| black l x (bin red (bin red rll rlx rlr) rx rr) := bin red (bin black l x rll) rlx (bin black rlr rx rr)
| black l x (bin red rl rx (bin red rrl rrx rrr)) := bin red (bin black l x rl) rx (bin black rrl rrx rrr)
| color l x r := bin color l x r

parameters [has_preordering E]

def insert_core (y : E) : rbtree E → rbtree E
| empty := bin red empty y empty
| (bin color l x r) :=
  match has_ordering.cmp y x with
  | ordering.lt := balanceL color (insert_core l) x r
  | ordering.eq := bin color l y r
  | ordering.gt := balanceR color l x (insert_core r)
  end

def insert (y : E) (t : rbtree E) : rbtree E := set_black (insert_core y t)

end insert


-----------------------------------------------------------------------
-- to_list

section to_list_theorems

theorem to_list_balanceL (c : color) (l r : rbtree E) (x : E)
: to_list (balanceL c l x r)  = to_list l ++ [x] ++ to_list r :=
begin
  cases c,
  tactic.swap,
  cases l with lc ll lx lr;
  try {
    cases lc;
    cases ll with llc lll llx llr; try { cases llc };
    cases lr with lrc lrl lrx lrr; try { cases lrc },
  },
  all_goals { simp [balanceL, to_list, *], },
end

theorem to_list_balanceR (c : color) (l r : rbtree E) (x : E)
: to_list (balanceR c l x r)  = to_list l ++ [x] ++ to_list r :=
begin
  cases c,
  tactic.swap,
  cases r with rc rl rx rr;
  try {
    cases rc;
    cases rl with rlc rll rlx rlr; try { cases rlc };
    cases rr with rrc rrl rrx rrr; try { cases rrc },
  },
  all_goals { simp [balanceR, to_list, *], },
end

parameters [has_preordering E]

theorem to_list_insert_core (y : E) (t : rbtree E)
: is_ordered t
→ to_list (insert_core y t)
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  induction t,
  case empty {
    simp [insert_core, to_list],
  },
  case bin color l x r l_ind r_ind {
    simp [insert_core, to_list, is_ordered, list.filter, key_is_lt, key_is_gt],

    have g1 : (ordering.gt ≠ ordering.lt), exact dec_trivial,
    have g2 : ordering.lt ≤ ordering.eq, exact dec_trivial,
    have g3 : ordering.eq ≤ ordering.eq, exact dec_trivial,
    have g4 : ordering.eq ≠ ordering.lt, exact dec_trivial,

    have cmp_k_key_eq : has_ordering.cmp x y = (has_ordering.cmp y x).swap,
    { rw [has_preordering.swap_cmp], },

    intros is_ordered_l is_ordered_r all_gt_r_x all_lt_l_x,
    have all_lt_r_key := all_lt_congr l x y,
    have all_gt_r_key := all_gt_congr r y x,
    have l_lt := filter_lt_of_all_lt l y,
    have l_gt := filter_gt_of_all_lt l y,
    have r_lt := filter_lt_of_all_gt r y,
    have r_gt := filter_gt_of_all_gt r y,

    destruct (has_ordering.cmp y x);
      intros cmp_key_k;
      simp [cmp_key_k, ordering.swap] at cmp_k_key_eq;
      simp [*, insert_core, to_list, to_list_balanceL, to_list_balanceR] at *,
  },
end

theorem to_list_insert (y : E) (t : rbtree E)
: is_ordered t → to_list (insert y t)
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  intros,
  simp [insert, to_list_set_black, to_list_insert_core, *],
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
-- is_ordered_insert

section is_ordered_theorems
parameters [has_preordering E]

def all_lt_balanceL (c : color) (y : E) (l r : rbtree E) (bnd : E)
  (all_lt_l : all_lt l y)
  (y_lt_bnd : has_ordering.cmp y bnd = ordering.lt)
  (all_lt_r : all_lt r bnd)
: all_lt (balanceL c l y r) bnd :=
begin
  cases c,
  tactic.swap,
  cases l with lc ll lx lr;
  try {
    cases lc;
    cases ll with llc lll llx llr; try { cases llc };
    cases lr with lrc lrl lrx lrr; try { cases lrc },
  },
  all_goals {
     try { simp [all_lt] at all_lt_l, },
     simp [balanceL, all_lt, *],
  },
  all_goals {
    apply has_preordering.lt_of_lt_of_lt _ y bnd _ y_lt_bnd,
    simp [*],
  },
end

def all_gt_balanceL (c : color) (y : E) (l r : rbtree E) (bnd : E)
  (iso : is_ordered l)
  (bnd_lt_y : has_ordering.cmp bnd y = ordering.lt)
  (all_gt_r : all_gt l bnd)
: all_gt (balanceL c l y r) bnd :=
begin
  cases c,
  tactic.swap,
  cases l with lc ll lx lr;
  try {
    cases lc;
    cases ll with llc lll llx llr; try { cases llc };
    cases lr with lrc lrl lrx lrr; try { cases lrc },
  },
  all_goals {
     try { simp [all_gt] at all_gt_r, },
     simp [balanceL, all_gt, *],
  },
  all_goals {
    simp [is_ordered, all_gt] at iso,
    apply has_preordering.lt_of_lt_of_lt bnd lx lrx; simp [*],
  },
end

def is_ordered_balanceL (c : color) (y : E) (l r : rbtree E)
  (iso_l : is_ordered l)
  (all_lt_l_y : all_lt l y)
  (all_gt_r_y : all_gt r y)
  (iso_r : is_ordered r)
: is_ordered (balanceL c l y r) :=
begin
  cases c,
  tactic.swap,
  cases l with lc ll lx lr;
  try {
    cases lc;
    cases ll with llc lll llx llr; try { cases llc };
    cases lr with lrc lrl lrx lrr; try { cases lrc },
  },
  all_goals {
    try { simp [is_ordered, all_lt, all_gt] at iso_l,},
    try { simp [all_lt] at all_lt_l_y, },
    simp [balanceL, all_lt, all_gt, is_ordered, *],
  },
end

def all_lt_balanceR (c : color) (y : E) (l r : rbtree E) (bnd : E)
  (iso : is_ordered r)
  (key_lt_u : has_ordering.cmp y bnd = ordering.lt)
  (all_lt_r : all_lt r bnd)
: all_lt (balanceR c l y r) bnd :=
begin
  cases c,
  tactic.swap,
  cases r with rc rl rx rr;
  try {
    cases rc;
    cases rl with rlc rll rlx rlr; try { cases rlc };
    cases rr with rrc rrl rrx rrr; try { cases rrc },
  },
  all_goals {
    try { simp [is_ordered, all_lt, all_gt] at iso, },
    try { simp [all_lt] at all_lt_r, },
    simp [balanceR, all_lt, *],
  },
  -- Remaining obligations have form:
  --  has_ordering.cmp rlx bnd = ordering.lt
  all_goals {
    apply has_preordering.lt_of_lt_of_lt rlx rx bnd; cc,
  },
end


def all_gt_balanceR (c : color) (y : E) (l r : rbtree E) (bnd : E)
  (iso : is_ordered r)
  (bnd_lt_y : has_ordering.cmp bnd y = ordering.lt)
  (all_gt_l : all_gt l bnd)
  (all_gt_r : all_gt r y)
: all_gt (balanceR c l y r) bnd :=
begin
  cases c,
  tactic.swap,
  cases r with rc rl rx rr;
  try {
    cases rc;
    cases rl with rlc rll rlx rlr; try { cases rlc };
    cases rr with rrc rrl rrx rrr; try { cases rrc },
  },

  all_goals {
    try { simp [is_ordered, all_lt, all_gt] at iso, },
    try { simp [all_gt] at all_gt_r, },
    simp [balanceR, all_gt, *],
  },
  all_goals {
    try { apply has_preordering.lt_of_lt_of_lt bnd y rx; cc, },
    try { apply has_preordering.lt_of_lt_of_lt bnd y rlx; cc, },
  },
end

def is_ordered_balanceR (c : color) (y : E) (l r : rbtree E)
  (iso_l : is_ordered l)
  (all_lt_l_y : all_lt l y)
  (all_gt_r_y : all_gt r y)
  (iso_r : is_ordered r)
: is_ordered (balanceR c l y r) :=
begin
  cases c,
  case red { simp [balanceR, is_ordered, *], },
  case black {
    cases r,
    case empty { simp [balanceR, is_ordered, *], },
    case bin lc ll lx lr {
      cases lc;
        cases ll with llc lll llx llr;
        try { cases llc };
        cases lr with lrc lrl lrx lrr;
        try { cases lrc },
      all_goals {
        simp [is_ordered, all_lt, all_gt] at iso_r,
        simp [all_gt] at all_gt_r_y,
        simp [balanceR, all_lt, all_gt, is_ordered, *],
      },
    },
  },
end


def insert_core_preserves (y : E) {t : rbtree E}
  (iso : is_ordered t)
: is_ordered (insert_core y t)
∧ (∀ (bnd : E),
    has_ordering.cmp y bnd = ordering.lt
               → all_lt t bnd
               → all_lt (insert_core y t) bnd)
∧ (∀ (bnd : E),
    has_ordering.cmp bnd y = ordering.lt
               → all_gt t bnd
               → all_gt (insert_core y t) bnd) :=
begin
  induction t,
  case empty {
    intros,
    simp [insert_core, all_lt, all_gt, is_ordered, *],
  },
  case bin c l x r l_ind r_ind {
    simp only [is_ordered] at iso,
    simp only [iso, true_implies_iff] at l_ind r_ind,
      destruct (has_ordering.cmp y x);
      intro cmp_y_s;
      simp only [cmp_y_s, insert_core, all_lt],
    { apply and.intro,
      { apply is_ordered_balanceL,
        apply and.left l_ind,
        apply and.left (and.right l_ind),
        all_goals { simp [*], },
      },
      apply and.intro,
      { intros bnd cmp_y_bnd pr,
        apply all_lt_balanceL,
        all_goals { simp [*], },
      },
      { intros bnd cmp_y_bnd pr,
        simp [all_gt] at pr,
        apply all_gt_balanceL,
        all_goals { simp [*], },
      }
    },
    { simp [is_ordered, *],
      apply and.intro,
      { apply all_gt_congr r y x; simp [*],
      },
      apply and.intro,
      { have h0 := has_preordering.eq_symm y x,
        apply all_lt_congr l x y; simp [*],
      },
      simp [all_gt],
      apply and.intro; cc,
    },
    { apply and.intro,
      { apply is_ordered_balanceR; try { cc, },
        { apply and.right (and.right r_ind);
            simp [has_preordering.gt_lt_symm, *] at *,
        },
      },
      apply and.intro,
      { intros,
        apply all_lt_balanceR; try { cc, },
        { apply and.left (and.right r_ind); cc, },
      },
      { simp [all_gt],
        intros,
        simp [has_preordering.gt_lt_symm, *] at *,
        apply all_gt_balanceR; try { cc },
        { apply and.left (and.right r_ind); cc, },
      },
    },
  },
end

theorem is_ordered_insert (y : E) (t : rbtree E)
: is_ordered t → is_ordered (insert y t) :=
begin
  intro iso,
  simp [insert],
  have h := insert_core_preserves y iso,
  cc,
end
end is_ordered_theorems

end insert
end rbtree
end data.containers
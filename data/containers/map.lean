/- This defines a map from key to values. -/
import .set

namespace data.containers

/-- A key value pair -/
structure binding (K : Type _) (A: Type _) :=
(key : K)
(value : A)

namespace binding
section
parameters {K : Type _} [has_preordering K]
parameters {    A: Type _}

def cmp (x y : binding K A) : ordering := has_ordering.cmp x.key y.key

instance : has_preordering (binding K A) :=
{ cmp := cmp
, refl := λx,
  begin
    cases x,
    simp [cmp], apply has_preordering.refl,
  end
, le_trans:= λa b c,
  begin
    cases a with ak, cases b with bk, cases c with ck,
    simp [cmp], apply has_preordering.le_trans,
  end
, gt_lt_symm:= λa b,
  begin
    cases a with ak, cases b with bk,
    simp [cmp], apply has_preordering.gt_lt_symm,
  end
}

def find_key (k : K) : binding K A → ordering := monotonic_find.eq k ∘ binding.key

instance (k : K) : monotonic_find (find_key k) :=
{ gt_increases := λ x y,
   @monotonic_find.gt_increases _ _ (monotonic_find.eq k) _ x.key y.key
, eq_preserves := λ x y,
   @monotonic_find.eq_preserves _ _ (monotonic_find.eq k) _ x.key y.key
, lt_decreases := λx y,
    @monotonic_find.lt_decreases _ _ (monotonic_find.eq k) _ x.key y.key
}

instance [decidable_eq K] [decidable_eq A] : decidable_eq (binding K A) :=
 by tactic.mk_dec_eq_instance

end
end binding

/-- A quotient map -/
def map (K : Type _) [has_preordering K] (A : Type _) :=
  set (binding K A)

namespace map
section
parameters {K : Type _} [has_preordering K] {A : Type _}

/-- Create the empty map. -/
def empty : map K A := set.empty

/-- Create a map with a single binding. -/
def singleton (k : K) (v : A) : map K A := set.singleton { key := k, value := v }

/-- Insert a binding from k to v into map. -/
def insert (k : K) (v : A) : map K A → map K A := set.insert { key := k, value := v }

/-- Lookup an element `x` in the set for which `p x = ordering.eq`. -/
def lookup (k : K) (m : map K A) : option A :=
  option.map binding.value (set.lookup (binding.find_key k) m)

/-- Return the ordered list of elements in the set. -/
def to_list : map K A → list (binding K A) := set.to_list

instance [decidable_eq K] [decidable_eq A] : decidable_eq (map K A) := by apply_instance

end
end map

end data.containers
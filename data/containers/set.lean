import .rbtree
import .rbtree.insert

namespace data.containers

-----------------------------------------------------------------------
-- ordered_tree

structure ordered_tree (E : Type _) [has_preordering E] :=
(tree : rbtree E)
(ordered : tree.is_ordered)
(wf : tree.well_formed)

namespace ordered_tree

section
parameters {E : Type _} [has_preordering E]

def empty : ordered_tree E :=
{ tree := rbtree.empty
, ordered := dec_trivial
, wf := dec_trivial
}

def singleton (x : E) : ordered_tree E :=
{ tree := rbtree.singleton x
, ordered := dec_trivial
, wf := dec_trivial
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
  apply rbtree.lookup_eq_of_to_list_eq; assumption,
end

end lookup

def insert (y : E) (t : ordered_tree E) : ordered_tree E :=
{ tree := rbtree.insert y t.tree
, ordered :=
  begin
    apply rbtree.is_ordered_insert _ _ t.ordered,
  end
, wf := rbtree.well_formed_insert y t.tree t.wf,
}

theorem insert_eq (y : E)
: ∀{t u : ordered_tree E},
   t.to_list = u.to_list
   → to_list (insert y t) = to_list (insert y u) :=
begin
  intros t u,
  unfold insert to_list,
  intros t_eq_u,
  simp [rbtree.to_list_insert y t.tree t.ordered, rbtree.to_list_insert y u.tree u.ordered, *],
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
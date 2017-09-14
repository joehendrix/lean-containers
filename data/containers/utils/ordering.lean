namespace ordering

protected
def le : ordering → ordering → Prop
| lt _ := true
| _ lt := false
| eq _ := true
| gt eq := false
| gt gt := true

instance : linear_order ordering :=
{ le := ordering.le
, le_refl     := λa, begin cases a; simp, end
, le_trans    := λa b c, begin cases a; cases b; cases c; simp [ordering.le], end
, le_antisymm := λa b, begin cases a; cases b; simp [has_le.le, ordering.le], end
, le_total    := λa b, begin cases a; cases b; simp [has_le.le, preorder.le, ordering.le], end
}

instance (x y : ordering) : decidable (x ≤ y) :=
begin
  cases x; cases y;
    simp [has_le.le, preorder.le, partial_order.le, linear_order.le, ordering.le];
    apply_instance,
end

end ordering

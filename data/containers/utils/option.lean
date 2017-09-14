/- Additional theroems for option. -/
namespace option

theorem failure_is_none (α : Type _) : (failure : option α) = none := rfl

theorem coe_is_some {α : Type _} (x:α) : (coe x : option α) = some x := rfl

theorem or_else_none {α : Type _} (x : option α) : (x <|> none) = x :=
begin
  cases x; trivial,
end

theorem none_or_else {α : Type _} (x : option α) : (none <|> x) = x :=
begin
  cases x; trivial,
end

theorem some_or_else {α : Type _} (x : α) (y : option α) : (some x <|> y) = some x :=
begin
  trivial,
end

end option

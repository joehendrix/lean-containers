/- Additional theroems for list. -/
import data.list
import .option

namespace list

theorem find_append {α : Type _} (p : α → Prop) [decidable_pred p] (x y : list α)
: list.find p (x ++ y) = (list.find p x <|> list.find p y) :=
begin
  induction x,
  case list.nil {
    simp [list.find, option.none_or_else],
  },
  case list.cons h r ind {
    simp [list.find, ind],
    by_cases (p h); simp [*, option.some_or_else],
  }
end

theorem find_cons {α : Type _} (p : α → Prop) [decidable_pred p] (x : α) (y : list α)
: list.find p (x :: y) = if p x then option.some x else y.find p := rfl

end list

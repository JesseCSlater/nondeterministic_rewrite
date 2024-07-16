import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic

abbrev Schema := Finset String

abbrev Row (scma : Schema) := (attr : String) → (attr ∈ scma) → Option Nat

abbrev Table scma := Multiset (Row scma)

inductive TExpr : (scma : Schema) → Type where
  | const :
    (Table scma) → TExpr scma
  | select :
    TExpr scma → (pred : Row scma → Prop) → [DecidablePred pred] → TExpr scma
  | nat_join :
    TExpr lscma → TExpr rscma → TExpr (lscma ∪ rscma)

def Table.select
  (table : Table scma) (pred : Row scma → Prop) [DecidablePred pred]
  : Table scma :=
  table.filter pred

def Row.nat_join
  (lrow : Row lscma) (rrow : Row rscma)
  : Row (lscma ∪ rscma)
  :=
  λ attr (_ : attr ∈ lscma ∪ rscma) =>
    if hl : attr ∈ lscma
    then lrow attr hl
    else if hr : attr ∈ rscma
    then rrow attr hr
    else none

def Row.union_left
  (row : Row (lscma ∪ rscma))
  : Row lscma
  := λ attr (mem : attr ∈ lscma) =>
    row attr (Finset.mem_union_left rscma mem)

def Row.union_right
  (row : Row (lscma ∪ rscma))
  : Row rscma
  := λ attr (mem : attr ∈ rscma) =>
    row attr (Finset.mem_union_right lscma mem)

theorem Row.row_eq_left_nat_join_right
  (row : Row (lscma ∪ rscma))
  : row = row.union_left.nat_join row.union_right
  := by
  unfold union_left nat_join union_right
  funext attr mem
  cases Finset.mem_union.mp mem
  · simp_all only [dite_true]
  · by_cases attr ∈ lscma
    <;> simp_all only [dite_false, dite_true]

def Row.cast_pred_union_left
  {lscma rscma : Schema} (pred : Row lscma → Prop) [DecidablePred pred]
  : Row (lscma ∪ rscma) → Prop
  := λ (row : Row (lscma ∪ rscma)) =>
    let lsubrow := λ attr (h : attr ∈ lscma) =>
      row attr (Finset.mem_union_left rscma h)
    pred lsubrow

section Row.cast_pred_union_left
instance {lscma rscma : Schema} (pred : Row lscma → Prop) [inst : DecidablePred pred]
  : DecidablePred (@Row.cast_pred_union_left lscma rscma pred inst) := by
  unfold Row.cast_pred_union_left
  infer_instance

theorem Row.cast_pred_eq_pred_left
  (row : Row (lscma ∪ rscma))
  (pred : Row lscma → Prop) [DecidablePred pred]
  : (cast_pred_union_left pred) row = pred row.union_left
  := by rfl
end Row.cast_pred_union_left

def Table.nat_join
  (ltable : Table lscma) (rtable : Table rscma)
  : Table (lscma ∪ rscma)
  :=
  ltable ×ˢ rtable
  |>.filter (λ (lrow, rrow) =>
    ∀ attr (mem_l : attr ∈ lscma) (mem_r : attr ∈ rscma),
      lrow attr mem_l = rrow attr mem_r)
  |>.map (λ (lrow, rrow) => lrow.nat_join rrow)

section Table.nat_join
theorem Multiset.product_count
  (M : Multiset α) (M' : Multiset β) (a : α) (b : β) [DecidableEq α] [DecidableEq β]
  : (M ×ˢ M').count (a, b) = M.count a * M'.count b
  := by
  induction M using Multiset.induction
  case empty => simp
  case cons head M ih =>
    by_cases a = head
    case neg neq =>
      simp_all only [cons_product, count_add, ne_eq, not_false_eq_true, count_cons_of_ne, add_left_eq_self, count_eq_zero, mem_map, Prod.mk.injEq, exists_eq_right_right, not_and]
      exact fun _ a_2 => neq (id (Eq.symm a_2))
    case pos eq =>
      simp_all only [cons_product, count_add, count_cons_self]
      rw [count_map_eq_count' _ _ (by unfold Function.Injective; simp)]
      ring

theorem Table.nat_join_count
  (ltable : Table lscma) (rtable : Table rscma)
  (row : Row (lscma ∪ rscma))
  : (ltable.nat_join rtable |> Multiset.count row) = ltable.count row.union_left * rtable.count row.union_right
  := by
  unfold nat_join
  simp only
  rw [Multiset.count_map, Multiset.filter_filter]
  rw [← Multiset.product_count, Multiset.count_eq_card_filter_eq]
  congr!
  rename_i pair
  constructor
  case mp =>
    unfold Row.union_left Row.union_right Row.nat_join
    simp_all only [dite_true, dite_eq_ite, ite_self, and_imp, implies_true]
  case mpr =>
    rintro rfl
    constructor
    · exact Row.row_eq_left_nat_join_right row
    · unfold Row.union_left Row.union_right
      simp_all only [implies_true]
end Table.nat_join

def TExpr.eval : TExpr scma → Table scma
  | const table =>
    table
  | select expr pred =>
    expr.eval |> (Table.select · pred)
  | nat_join lexpr rexpr =>
    Table.nat_join lexpr.eval rexpr.eval

def TExpr.equals
  (orig rewrite : TExpr scma)
  : Prop
  := rewrite.eval = orig.eval
infix:0 " =ᵣ " => TExpr.equals

theorem TExpr.select_past_join_left
  (lexpr : TExpr lscma) (rexpr : TExpr rscma)
  (pred : (Row lscma → Prop)) [DecidablePred pred]
  : nat_join (select lexpr pred) rexpr =ᵣ
    select (nat_join lexpr rexpr) (Row.cast_pred_union_left pred)
  := by
  unfold TExpr.equals
  simp_rw [TExpr.eval]
  ext row
  unfold Table.select
  rw [Table.nat_join_count]
  by_cases row.cast_pred_union_left pred
  case neg neq =>
    simp_all [Row.union_left, Row.union_right, Row.cast_pred_eq_pred_left]
  case pos eq =>
    simp_all [Row.union_left, Row.union_right, Row.cast_pred_eq_pred_left,
      Table.nat_join_count]

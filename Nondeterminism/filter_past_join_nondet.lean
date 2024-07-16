import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

abbrev Schema := Finset String

abbrev Row (scma : Schema) := (attr : String) → (attr ∈ scma) → Option Nat

abbrev Table scma := List (Row scma)

abbrev NTable scma := Finset (Table scma)

inductive NTExpr : (scma : Schema) → Type where
  | const :
    (NTable scma) → NTExpr scma
  | select :
    NTExpr scma → (pred : Row scma → Prop) → [DecidablePred pred] → NTExpr scma
  | nat_join :
    NTExpr lscma → NTExpr rscma → NTExpr (lscma ∪ rscma)

def Table.forget_order
  (table : Table scma)
  : NTable scma :=
  table.permutations |>.toFinset

section Table.forget_order
theorem Table.mem_forget_order_self
  (table : Table scma)
  : table ∈ table.forget_order
  := by
  simp_all only [forget_order, List.mem_toFinset, List.mem_permutations, List.Perm.refl]

@[simp]
theorem Table.mem_forget_order_iff
  (table table' : Table scma)
  : table' ∈ table.forget_order ↔ table.Perm table'
  := by
  simp_all only [forget_order, List.mem_toFinset, List.mem_permutations, Multiset.coe_eq_coe, List.perm_comm]
end Table.forget_order

abbrev Table.t_select
  (table : Table scma) (pred : Row scma → Prop) [DecidablePred pred]
  : Table scma :=
  table.filter pred

def Table.select
  (table : Table scma) (pred : Row scma → Prop) [DecidablePred pred]
  : NTable scma :=
  table.t_select pred |> Table.forget_order

section Table.select
theorem Table.mem_select_self
  (table : Table scma) (pred : Row scma → Prop) [DecidablePred pred]
  : table.filter pred ∈ table.select pred
  := by
  simp_all only [select, mem_forget_order_self]

@[simp]
theorem Table.mem_select_iff
  {table : Table scma} {pred : Row scma → Prop} [DecidablePred pred]
  : table' ∈ table.select pred ↔ table'.Perm (table.filter pred)
  := by
  unfold select forget_order
  simp only [List.mem_toFinset, List.mem_permutations]
end Table.select

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

def Table.t_nat_join
  (ltable : Table lscma) (rtable : Table rscma)
  : Table (lscma ∪ rscma)
  :=
  ltable ×ˢ rtable
  |>.filter (λ (lrow, rrow) =>
    ∀ attr (mem_l : attr ∈ lscma) (mem_r : attr ∈ rscma),
      lrow attr mem_l = rrow attr mem_r)
  |>.map (λ (lrow, rrow) => lrow.nat_join rrow)

def Table.nat_join
  (ltable : Table lscma) (rtable : Table rscma)
  : NTable (lscma ∪ rscma)
  :=
  Table.t_nat_join ltable rtable
  |> Table.forget_order

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

theorem Table.t_nat_join_count
  (ltable : Table lscma) (rtable : Table rscma)
  (row : Row (lscma ∪ rscma))
  : (ltable.t_nat_join rtable |> List.count row) = ltable.count row.union_left * rtable.count row.union_right
  := by
  unfold t_nat_join
  simp only [← Multiset.coe_count, ← Multiset.map_coe, ← Multiset.filter_coe, ← Multiset.coe_product]
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

def NTExpr.eval : NTExpr scma → NTable scma
  | const ntable =>
    ntable
  | select expr pred =>
    expr.eval
    |>.sup (Table.select · pred)
  | nat_join lexpr rexpr =>
    lexpr.eval ×ˢ rexpr.eval
    |>.sup (λ (ltable, rtable) => Table.nat_join ltable rtable)

def NTExpr.rewrites_to
  (orig rewrite : NTExpr scma)
  : Prop
  := rewrite.eval ⊆ orig.eval
infix:0 " =>ᵣ " => NTExpr.rewrites_to

theorem NTExpr.select_past_join_left
  (lexpr : NTExpr lscma) (rexpr : NTExpr rscma)
  (pred : (Row lscma → Prop)) [DecidablePred pred]
  : nat_join (select lexpr pred) rexpr =>ᵣ
    select (nat_join lexpr rexpr) (Row.cast_pred_union_left pred)
  := by
  unfold NTExpr.rewrites_to
  simp_rw [NTExpr.eval]
  rw [Finset.subset_iff]
  intro table elem
  rw [Finset.mem_sup] at elem
  rcases elem with ⟨unfiltered_table, elem, table_filtered⟩
  rw [Finset.mem_sup] at elem
  rcases elem with ⟨table_pair, elem, unfiltered_table_paired⟩
  rcases table_pair with ⟨left_table, right_table⟩
  rw [Finset.mem_sup]
  use (left_table.filter pred, right_table)
  simp_all only [Finset.mem_product, and_true]
  constructor
  case left =>
    rw [Finset.mem_sup]
    use left_table
    simp_all only [Table.mem_select_self, and_self]
  case right =>
    simp_all only [Table.mem_select_iff, Table.nat_join,
      Table.mem_forget_order_iff, ← Multiset.coe_eq_coe]
    ext row
    by_cases row.cast_pred_union_left pred
    case neg neq =>
      rw [← Multiset.filter_coe, ← unfiltered_table_paired,
        Multiset.count_filter_of_neg neq]
      simp_all only [Row.cast_pred_eq_pred_left, Multiset.coe_eq_coe,
        Multiset.coe_count, Table.t_nat_join_count, mul_eq_zero]
      rw [← Multiset.coe_count, ← Multiset.filter_coe]
      exact Or.intro_left _ (Multiset.count_filter_of_neg neq)
    case pos eq =>
      rw [← Multiset.filter_coe, ←unfiltered_table_paired,
        Multiset.count_filter_of_pos eq]
      simp_all only [Row.cast_pred_eq_pred_left, Multiset.coe_eq_coe,
        Multiset.coe_count, Table.t_nat_join_count, decide_True,
        List.count_filter]

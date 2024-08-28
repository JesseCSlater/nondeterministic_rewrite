import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic
import Mathlib

abbrev Row (n : Nat) := Fin n → Option Nat

abbrev Table n := List (Row n)

structure NTable (n : Nat) where
  s : Set (Table n)
  w : Table n
  mem : w ∈ s

def NTable.bind
  (nt : NTable n) (f : Table n → NTable m)
  : NTable m where
  s := ⋃ t ∈ nt.s, (f t).s
  w := (f nt.w).w
  mem := by
    simp_all only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
    use nt.w
    exact ⟨nt.mem, (f nt.w).mem⟩
infix:67 " >>= " => NTable.bind

def NTable.bind₂
  (ntl : NTable ln) (ntr : NTable rn) (f : Table ln → Table rn → NTable m)
  : NTable m where
  s := ⋃ lt ∈ ntl.s, ⋃ rt ∈ ntr.s, (f lt rt).s
  w := (f ntl.w ntr.w).w
  mem := by 
    simp_all only [Set.mem_iUnion, exists_prop]
    use ntl.w
    refine ⟨ntl.mem, ?_⟩
    use ntr.w
    refine ⟨ntr.mem, ?_⟩
    exact (f ntl.w ntr.w).mem

inductive RowExpr : (n : Nat) → Type where
  | const : 
    Row n → RowExpr n

inductive ValExpr where
  | const : 
    Nat → ValExpr
  | access : 
    RowExpr n → Fin n → ValExpr

inductive PredExpr where
  | const : 
    Prop → PredExpr
  | and : 
    PredExpr → PredExpr → PredExpr
  | or : 
    PredExpr → PredExpr → PredExpr
  | not :
    PredExpr → PredExpr
  | eq : 
    ValExpr → ValExpr → PredExpr
  | neq : 
    ValExpr → ValExpr → PredExpr
  | lt : 
    ValExpr → ValExpr → PredExpr

inductive NTExpr : (n : Nat) → Type where
  | const :
    NTable n → NTExpr n
  | project :
    NTExpr n → (Fin m ↪ Fin n) → NTExpr m
  | filter :
    NTExpr n → (pred : Row n → Prop) → [DecidablePred pred] → NTExpr n
  | prod :
    NTExpr l → NTExpr r → NTExpr (l + r)
  | sort : 
    NTExpr n → (rel : Row n → Row n → Prop) → (Transitive rel) → (Total rel) → [DecidableRel rel] → NTExpr n

def Table.t_filter
  (table : Table n) (pred : Row n → Prop) [DecidablePred pred]
  : Table n :=
  table.filter pred

def Table.n_filter
  (table : Table n) (pred : Row n → Prop) [DecidablePred pred]
  : NTable n where
  s := {table.t_filter pred}
  w := table.t_filter pred
  mem := by rfl

def Table.t_project
  (table : Table n) (f : Fin m ↪ Fin n)
  : Table m :=
  table.map (· ∘ f)

def Table.n_project
  (table : Table n) (f : Fin m ↪ Fin n)
  : NTable m where
  s := {table.t_project f}
  w := table.t_project f
  mem := by rfl

def Table.t_prod
  (ltable : Table l) (rtable : Table r)
  : Table (l + r) :=
  List.product ltable rtable
  |>.map fun (lrow, rrow) (lr : Fin (l + r)) ↦  Fin.addCases lrow rrow lr

def Table.n_prod
  (ltable : Table l) (rtable : Table r)
  : NTable (l + r) where
  s := {Table.t_prod ltable rtable}
  w := Table.t_prod ltable rtable
  mem := by rfl

def Table.n_sort
  (table : Table n) (rel : Row n → Row n → Prop) 
  (trans : Transitive rel) (total : Total rel) [DecidableRel rel]
  : NTable n where
  s := fun t ↦  table.Perm t ∧ List.Pairwise rel t
  w := table.insertionSort rel
  mem := by --long proof
    have is_pairwise : List.Pairwise rel (List.insertionSort rel table) := by 
      induction table with 
      | nil => simp_all only [List.insertionSort, List.Pairwise.nil]
      | cons head tail ih =>
        rw [List.insertionSort_cons_eq_take_drop]
        rw [List.pairwise_append]
        have head_pairwise : List.Pairwise rel (head :: List.dropWhile (fun b => decide ¬rel head b) (List.insertionSort rel tail)) := by
          rw [List.pairwise_cons]
          constructor
          case right =>
            apply List.Pairwise.sublist ?_ ih
            apply List.IsSuffix.sublist
            apply List.dropWhile_suffix
          case left =>
            intro row row_mem
            cases h : List.dropWhile (fun b => decide ¬rel head b) (List.insertionSort rel tail) with
            | nil =>
              rw [h] at row_mem
              simp_all only [List.not_mem_nil]
            | cons head' tail' => 
              have sublist : (head' :: tail').Sublist (List.insertionSort rel tail) := by 
                rw [← h]
                apply List.IsSuffix.sublist
                apply List.dropWhile_suffix
              apply List.Pairwise.sublist sublist at ih
              rw [h] at row_mem
              have rel_head : rel head head' := by 
                have head_false := List.head_dropWhile_not (fun b => decide ¬rel head b) (List.insertionSort rel tail) (by simp_all only [List.mem_cons, decide_not, List.pairwise_cons, ne_eq, not_false_eq_true])
                simp_rw [h] at head_false
                simp_all only [List.mem_cons, List.pairwise_cons, List.head_cons, decide_not, Bool.not_eq_false', decide_eq_true_eq]
              apply trans rel_head
              rw [List.mem_cons] at row_mem
              rcases row_mem 
              case cons.inl row_eq =>
                specialize total head' head'
                simp_all only [decide_not, List.pairwise_cons, or_self]
              case cons.inr row_eq =>
                rw [List.pairwise_cons] at ih
                exact ih.left row row_eq 
        refine ⟨?take, ?drop, ?_⟩
        case take =>
          apply List.Pairwise.sublist ?_ ih
          apply List.IsPrefix.sublist
          apply List.takeWhile_prefix
        case drop => exact head_pairwise
        case cons =>
          intro row row_mem row' row'_mem
          rw [List.mem_cons] at row'_mem
          apply List.mem_takeWhile_imp at row_mem
          simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at row_mem
          rcases row'_mem 
          case inl h =>
            obtain rfl := h
            specialize total row row' 
            simp_all only [or_false]
          case inr h =>
            specialize total head row 
            simp_all only [decide_not, false_or]
            apply trans total
            rw [List.pairwise_cons] at head_pairwise
            exact head_pairwise.left row' h
    exact ⟨List.Perm.symm (List.perm_insertionSort rel table), is_pairwise⟩

theorem Table.n_sort_eq_sort_perm
  (table table' : Table n) (rel : Row n → Row n → Prop) (trans : Transitive rel) (total : Total rel) [DecidableRel rel] (perm : table.Perm table')
  : (table.n_sort rel trans total).s = (table'.n_sort rel trans total).s
  := by
  unfold n_sort
  simp only
  ext t
  constructor
  <;> rintro ⟨perm', pairwise⟩ 
  <;> refine ⟨List.Perm.trans ?_ perm', pairwise⟩
  · exact List.Perm.symm perm
  · exact perm

def NTExpr.eval : NTExpr scma → NTable scma
  | const ntable =>
    ntable
  | filter expr pred =>
    expr.eval >>= (Table.n_filter · pred)
  | project expr f =>
    expr.eval >>= (Table.n_project · f)
  | prod lexpr rexpr =>
    NTable.bind₂ lexpr.eval rexpr.eval Table.n_prod
  | sort expr rel transitive total =>
    expr.eval >>= (Table.n_sort · rel transitive total)

def NTExpr.rewrites_to
  (orig rewrite : NTExpr scma)
  : Prop
  := rewrite.eval.s ⊆ orig.eval.s
infix:0 " =>ᵣ " => NTExpr.rewrites_to

theorem remove_redundant_sort
  (input : NTExpr n) (rel rel' : Row n → Row n → Prop) (trans : Transitive rel) (trans' : Transitive rel') (total : Total rel) (total' : Total rel') [DecidableRel rel] [DecidableRel rel']
  : NTExpr.sort input rel' trans' total' |>.sort rel trans total =>ᵣ NTExpr.sort input rel trans total
  := by
  unfold NTExpr.rewrites_to
  simp_rw [NTExpr.eval, NTable.bind]
  simp_all only [Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and', Set.iUnion_subset_iff]
  intro table mem
  apply subset_trans ?_ (Set.subset_biUnion_of_mem mem)
  apply subset_trans ?_ (Set.subset_biUnion_of_mem (table.n_sort rel' trans' total').mem)
  unfold Table.n_sort
  simp only
  rintro table' ⟨perm, sorted⟩  
  exact ⟨List.Perm.trans (List.perm_insertionSort rel' table) perm, sorted⟩ 








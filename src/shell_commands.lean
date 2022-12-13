import data.list.sort
import data.string.basic
import .utils

/-

tr -cs A-Za-z '
' |
tr A-Z a-z |
sort |
uniq -c |
sort -rn

-/

namespace shell

-- represents a line of data in a stream-of-strings where each column
-- is associated with a type
def record : Type := list string

-- aliases for per-line predicates (line_pred) and between-line predicates (doc_pred)
def line_pred : Type := record → Prop
def doc_pred : Type := list record → Prop

-- custom types 
inductive type : Type
| str : type
| num : type

-- represents a stream-of-string datum that is refined by a set of per-line and
-- between-line predicates
structure stream_of_strings :=
  (records : list record)
  (column_types : list type)
  (per_line : list line_pred)
  (bet_line : list doc_pred)

instance : has_repr record := ⟨λ r, utils.list_to_string r⟩
instance : has_repr stream_of_strings := ⟨λ sos, list.repr sos.records⟩

-- TODO: why can't I use keyword `lemma` here? 

/-                                  -/
/-               SORT               -/
/-                                  -/

-- ordering predicates on pairs of records (order ascdending or descending by the first column)
-- TODO: make more sophisticated (if first col is equal, move to second col and so on)
def record_le : record → record → Prop 
| r1 r2 := (list.head r1) ≤ (list.head r2)
def record_gt : record → record → Prop
| r1 r2 := (list.head r1) > (list.head r2)

instance : has_le record := { le := λ r1 r2, record_le r1 r2, }

instance : decidable_rel record_le :=
begin
  rw decidable_rel,
  intros r1 r2,
  apply string.decidable_le,
end

instance : decidable_rel record_gt :=
begin
  rw decidable_rel,
  intros r1 r2,
  apply string.decidable_lt,
end

-- sort a list of records ascending
def sort_asc (rs : list record) : list record := list.merge_sort record_le rs 
-- sort a list of records descending
def sort_des (rs : list record) : list record := list.merge_sort record_gt rs 


-- sorted predicates on a list of records
def sorted_asc : list record → Prop 
| r := list.sorted record_le r
def sorted_des : list record → Prop 
| r := list.sorted record_gt r

-- sort
-- sort in ascending order
def sort : stream_of_strings → stream_of_strings
| r := { records := sort_asc r.records,
         column_types := r.column_types,
         per_line := r.per_line,
         bet_line := [sorted_asc] }

-- sort -r
-- sort in descending order
def sort_r : stream_of_strings → stream_of_strings 
| r := { records := sort_des r.records,
         column_types := r.column_types,
         per_line := r.per_line,
         bet_line := [sorted_des] }

-- sort -n
-- sort in ascending order, first column has numeric type
def sort_n_hlp : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_asc sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_asc]}
| _ _ := none
def sort_n : stream_of_strings → option stream_of_strings
| r := sort_n_hlp r r.column_types

-- sort -rn
-- sort in descending order, first column has numeric type
def sort_rn_hlp [h_gt : decidable_rel record_gt] : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_des sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_des]}
| _ _ := none
def sort_rn (input : stream_of_strings) [h_gt : decidable_rel record_gt]: option stream_of_strings := 
  sort_rn_hlp input input.column_types

/-                                  -/
/-               UNIQ               -/
/-                                  -/

-- a predicate that says "no adjacent lines are the same"
def adj_lines_uniq (input : list record) : Prop := sorry

-- collapse adjacent duplicate records
def make_uniq : list record → list record 
| (r1 :: (r2 :: rs)) := if r1 = r2 
                        then (r1 :: make_uniq rs) 
                        else (r1 :: (r2 :: make_uniq rs))
| e := e

-- collapse adjacent duplicate records and prefix records with a count
def prefix_init_count : list record → list record 
| (r :: rs) := (((to_string 1) :: r) :: prefix_init_count rs)
| [] := []
def make_uniq_c_hlp : list record → list record 
| ((cnt1 :: rs1) :: ((cnt2 :: rs2) :: rs)) := if rs1 = rs2 
                                              then ((to_string ((utils.string_to_nat cnt1) + (utils.string_to_nat cnt2)) :: rs1) :: make_uniq rs) 
                                              else ((cnt1 :: rs1) :: ((cnt2 :: rs2) :: make_uniq rs))
| e := e
def make_uniq_c : list record → list record 
| rs := make_uniq_c_hlp (prefix_init_count rs)

-- uniq
-- filter out adjacent repeated lines
def uniq (input : stream_of_strings) : stream_of_strings := 
  { records := make_uniq input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }

-- uniq -c
-- filter out adjacent repeated lines and prefix the lines with 
-- a count column
def uniq_c (input : stream_of_strings) : stream_of_strings := 
  { records := make_uniq_c input.records,
    column_types := type.num :: input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }

/-                                  -/
/-           DECIDABILITY           -/
/-                                  -/

-- TODO: need string.le_trans
def record_linear_order : linear_order record :=
{ le := record_le,
  le_refl := begin intro a, simp, rw record_le, simp end,
  le_trans := begin intros a b c, simp, repeat {rw record_le}, intros hab hbc, sorry end,
  lt_iff_le_not_le := sorry,
  le_antisymm := sorry,
  le_total := sorry,
  decidable_le := record_le.decidable_rel, }

/-                                  -/
/-           VERIFICATION           -/
/-                                  -/

def my_sos : stream_of_strings :=
{ records := [["Hello", " ", "world!"],
              ["Hello", " ", "world!"],
              ["Why,", " ", "hello."],
              ["Hello", " ", "world!"],
              ["ABC"],
              ["ABC"],
              ["ABC", " "]],
  column_types := [type.str, type.str, type.str],
  per_line := [],
  bet_line := [] }

def my_sos_uniq : stream_of_strings := uniq my_sos
def my_sos_uniq_c : stream_of_strings := uniq_c my_sos
def my_sos_sort : stream_of_strings := sort my_sos
def my_sos_sort_r : stream_of_strings := sort_r my_sos

#eval my_sos_uniq.records
#eval my_sos_uniq_c.records
#eval my_sos_sort.records
#eval my_sos_sort_r.records

-- a composition of sorts flattens to the outermost sort, 
-- in this case composing sort_r with sort
lemma sort_composition (sos : stream_of_strings) [h_le : decidable_rel record_le] [h_gt : decidable_rel record_gt] : sort sos = sort (sort_r sos) :=
begin
  sorry
end

-- sorting then doing uniq produces a stream of strings without duplicate lines
lemma sort_then_uniq_nodup (sos : stream_of_strings) [h_le : decidable_rel record_le] [h : linear_order record] : list.nodup (uniq (sort sos)).records :=
begin
  sorry
end

end shell
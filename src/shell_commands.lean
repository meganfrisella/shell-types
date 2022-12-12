import data.list.sort
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

/-                                  -/
/-               SORT               -/
/-                                  -/

-- ordering predicates on pairs of records (order ascdending or descending by the first column)
-- TODO: make more sophisticated (if first col is equal, move to second col and so on)
def record_asc : record → record → Prop 
| r1 r2 := (list.head r1) < (list.head r2)
def record_des : record → record → Prop 
| r1 r2 := (list.head r1) > (list.head r2)

-- sort a list of records ascending
def sort_asc [h_asc : decidable_rel record_asc] : list record → list record 
| r := list.merge_sort record_asc r
-- sort a list of records descending
def sort_des [h_des : decidable_rel record_des] : list record → list record 
| r := list.merge_sort record_des r

-- sorted predicates on a list of records
def sorted_asc : list record → Prop 
| r := list.sorted record_asc r
def sorted_des : list record → Prop 
| r := list.sorted record_des r

-- sort
-- sort in ascending order
def sort [h_asc : decidable_rel record_asc] : stream_of_strings → stream_of_strings
| r := { records := sort_asc r.records,
         column_types := r.column_types,
         per_line := r.per_line,
         bet_line := [sorted_asc] }

-- sort -r
-- sort in descending order
def sort_r [h_des : decidable_rel record_des] : stream_of_strings → stream_of_strings 
| r := { records := sort_des r.records,
         column_types := r.column_types,
         per_line := r.per_line,
         bet_line := [sorted_des] }

-- sort -n
-- sort in ascending order, first column has numeric type
def sort_n_hlp [h_asc : decidable_rel record_asc] : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_asc sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_asc]}
| _ _ := none
def sort_n [h_asc : decidable_rel record_asc] : stream_of_strings → option stream_of_strings
| r := sort_n_hlp r r.column_types

-- sort -rn
-- sort in descending order, first column has numeric type
def sort_rn_hlp [h_des : decidable_rel record_des] : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_des sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_des]}
| _ _ := none
def sort_rn (input : stream_of_strings) [h_des : decidable_rel record_des]: option stream_of_strings := 
  sort_rn_hlp input input.column_types

/-                                  -/
/-               UNIQ               -/
/-                                  -/

-- a predicate that says "no adjacent lines are the same"
def adj_lines_uniq (input : list record) : Prop := sorry

-- collapse adjacent duplicate records
def make_uniq [h : linear_order record] : list record → list record 
| (r1 :: (r2 :: rs)) := if r1 = r2 
                        then (r1 :: make_uniq rs) 
                        else (r1 :: (r2 :: make_uniq rs))
| e := e

-- collapse adjacent duplicate records and prefix records with a count
def prefix_init_count : list record → list record 
| (r :: rs) := (((to_string 1) :: r) :: prefix_init_count rs)
| [] := []
def make_uniq_c_hlp [h : linear_order record] : list record → list record 
| ((cnt1 :: rs1) :: ((cnt2 :: rs2) :: rs)) := if rs1 = rs2 
                                              then ((to_string ((utils.string_to_nat cnt1) + (utils.string_to_nat cnt2)) :: rs1) :: make_uniq rs) 
                                              else ((cnt1 :: rs1) :: ((cnt2 :: rs2) :: make_uniq rs))
| e := e
def make_uniq_c [h : linear_order record] : list record → list record 
| rs := make_uniq_c_hlp (prefix_init_count rs)

-- uniq
-- filter out adjacent repeated lines
def uniq (input : stream_of_strings) [h : linear_order record] : stream_of_strings := 
  { records := make_uniq input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }

-- uniq -c
-- filter out adjacent repeated lines and prefix the lines with 
-- a count column
def uniq_c (input : stream_of_strings) [h : linear_order record] : stream_of_strings := 
  { records := make_uniq_c input.records,
    column_types := type.num :: input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }

/-                                  -/
/-           VERIFICATION           -/
/-                                  -/

-- prove `decidable_rel record_asc` as a separate lemma
-- prove `decidable_rel record_des` as a separate lemma
-- prove `linear_order record` as a separate lemma

def my_sos : stream_of_strings :=
{ records := [["Hello", " ", "world!"],
              ["Why,", " ", "hello."],
              ["Hello", " ", "world!"]],
  column_types := [type.str, type.str, type.str],
  per_line := [],
  bet_line := [] }

-- a composition of sorts flattens to the outermost sort, 
-- in this case composing sort_r with sort
lemma sort_composition (sos : stream_of_strings) [h_asc : decidable_rel record_asc] [h_des : decidable_rel record_des] : sort sos = sort (sort_r sos)
  := sorry

-- sorting then doing uniq produces a stream of strings without duplicate lines
lemma sort_then_uniq_nodup (sos : stream_of_strings) [h_asc : decidable_rel record_asc] [h : linear_order record] : list.nodup (uniq (sort sos)).records
  := sorry

end shell
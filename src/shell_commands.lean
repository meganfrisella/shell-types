import data.list.sort

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
structure record := (columns : list string)

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

/-----------------------------------------
|                  SORT                  |
-----------------------------------------/

-- ordering predicates on pairs of records (order ascdending or descending by the first column)
-- TODO: make more sophisticated (if first col is equal, move to second col and so on)
def record_asc (r1 r2 : record) : Prop := (list.head r1.columns) < (list.head r2.columns)
def record_des (r1 r2 : record) : Prop := (list.head r1.columns) > (list.head r2.columns)

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

/-----------------------------------------
|                  UNIQ                  |
-----------------------------------------/

-- a predicate that says "no adjacent lines are the same"
def adj_lines_uniq (input : list record) : Prop := sorry

-- collapse adjacent duplicate records
def make_uniq : list record → list record 
| (r1 :: (r2 :: rs)) := sorry -- TODO: want: if r1 == r2 then r1 :: make_uniq rs else r1 :: r2 :: make_uniq rs
| [r] := [r]
| [] := []
-- collapse adjacent duplicate records and prefix records with a count
def make_uniq_c : list record → list record 
| (r1 :: (r2 :: rs)) := sorry -- TODO: as above
| [r] := [r]
| [] := []

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

/-----------------------------------------
|              VERIFICATION              |
-----------------------------------------/

-- a composition of sorts flattens to the outermost sort, 
-- in this case composing sort_r with sort
lemma sort_composition (sos : stream_of_strings) [h_asc : decidable_rel record_asc] [h_des : decidable_rel record_des] : sort sos = sort (sort_r sos)
  := sorry

-- sorting then doing uniq produces a stream of strings without duplicate lines
lemma sort_then_uniq_nodup (sos : stream_of_strings) [h_asc : decidable_rel record_asc]: list.nodup (uniq (sort sos)).records
  := sorry

end shell
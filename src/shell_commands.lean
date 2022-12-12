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

-- ordering predicates on records (sort ascdending or descending by the first column)
-- TODO: this can be more sophisticated (if first col is equal, move to second col and so on)
def record_asc (r1 r2 : record) : Prop := (list.head r1.columns) < (list.head r2.columns)
def record_des (r1 r2 : record) : Prop := (list.head r1.columns) > (list.head r2.columns)

-- sort a list of records ascending and descending
def sort_asc (input : list record) [h_asc : decidable_rel record_asc] : list record 
  := list.merge_sort record_asc input
def sort_des (input : list record) [h_des : decidable_rel record_des] : list record 
  := list.merge_sort record_des input

-- four ordering predicates, one for each sort variant
def sorted_asc (input : list record) : Prop := list.sorted record_asc input
def sorted_des (input : list record) : Prop := list.sorted record_des input

-- sort
-- sort alphabetically in ascending order
-- no requirements on input
def sort (input : stream_of_strings) [h_asc : decidable_rel record_asc] : stream_of_strings := 
  { records := sort_asc input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [sorted_asc] }

-- sort -r
-- sort alphabetically in descending order
-- no requirements on input
def sort_r (input : stream_of_strings) [h_des : decidable_rel record_des] : stream_of_strings := 
  { records := sort_des input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [sorted_des] }

-- sort -n
-- sort numerically in ascending order
-- helper checks that the first column has numeric type
def sort_n_helper [h_asc : decidable_rel record_asc] : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_asc sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_asc]}
| _ _ := none
def sort_n (input : stream_of_strings) [h_asc : decidable_rel record_asc] : option stream_of_strings := 
  sort_n_helper input input.column_types

-- sort -rn
-- sort numerically in descending order
-- helper checks that the first column has numeric type
def sort_rn_helper [h_des : decidable_rel record_des] : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := sort_des sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [sorted_des]}
| _ _ := none
def sort_rn (input : stream_of_strings) [h_des : decidable_rel record_des]: option stream_of_strings := 
  sort_rn_helper input input.column_types

/-----------------------------------------
|                  UNIQ                  |
-----------------------------------------/

-- a predicate that says "no adjacent lines are the same"
def adj_lines_uniq (input : list record) : Prop := sorry

-- implementations of the two uniq functions
def make_uniq (input : list record) : list record := sorry
def make_uniq_c (input : list record) : list record := sorry

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

theorem sort_then_uniq_nodup (input : stream_of_strings) [h_asc : decidable_rel record_asc]: list.nodup (sort (uniq input)).records
  := sorry

end shell
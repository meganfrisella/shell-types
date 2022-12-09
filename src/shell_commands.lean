namespace shell

/-

tr -cs A-Za-z '
' |
tr A-Z a-z |
sort |
uniq -c |
sort -rn

-/

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

-- four ordering predicates, one for each sort variant
-- along with corresponding ordering functions
constants has_def_order has_r_order has_n_order has_rn_order : doc_pred
axiom make_sort : list record → list record
axiom make_sort_r : list record → list record
axiom make_sort_n : list record → list record
axiom make_sort_rn : list record → list record

-- sort
-- sort alphabetically in ascending order
-- no requirements on input
noncomputable def sort (input : stream_of_strings) : stream_of_strings := 
  { records := make_sort input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [has_def_order] }

-- sort -r
-- sort alphabetically in descending order
-- no requirements on input
noncomputable def sort_r (input : stream_of_strings) : stream_of_strings := 
  { records := make_sort_r input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [has_r_order] }

-- sort -n
-- sort numerically in ascending order
-- helper checks that the first column has numeric type
noncomputable def sort_n_helper : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := make_sort_n sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [has_n_order]}
| _ _ := none
noncomputable def sort_n (input : stream_of_strings) : option stream_of_strings := 
  sort_n_helper input input.column_types

-- sort -rn
-- sort numerically in descending order
-- helper checks that the first column has numeric type
noncomputable def sort_rn_helper : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := make_sort_rn sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [has_rn_order]}
| _ _ := none
noncomputable def sort_rn (input : stream_of_strings) : option stream_of_strings := 
  sort_n_helper input input.column_types

/-----------------------------------------
|                  UNIQ                  |
-----------------------------------------/

-- a predicate that says "no adjacent lines are the same"
-- along with corresponding uniq functions
constants adj_lines_uniq : doc_pred
axiom make_uniq : list record → list record
axiom make_uniq_c : list record → list record

-- uniq
-- filter out adjacent repeated lines
noncomputable def uniq (input : stream_of_strings) : stream_of_strings := 
  { records := make_uniq input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }
-- uniq -c
-- filter out adjacent repeated lines and prefix the lines with 
-- a count column
noncomputable def uniq_c (input : stream_of_strings) : stream_of_strings := 
  { records := make_uniq_c input.records,
    column_types := type.num :: input.column_types,
    per_line := input.per_line,
    bet_line := adj_lines_uniq :: input.bet_line }

/-----------------------------------------
|              VERIFICATION              |
-----------------------------------------/

def no_duplicate_lines : stream_of_strings → Prop := sorry
theorem sort_then_uniq (input : stream_of_strings) : no_duplicate_lines (sort (uniq input))
  := sorry

end shell
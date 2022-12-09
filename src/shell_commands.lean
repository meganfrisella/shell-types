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
def has_def_order (input : list record) : Prop := sorry
def has_r_order (input : list record) : Prop := sorry
def has_n_order (input : list record) : Prop := sorry
def has_rn_order (input : list record) : Prop := sorry

-- implementations of the four ordering functions
def make_sort (input : list record) : list record := sorry
def make_sort_r (input : list record) : list record := sorry
def make_sort_n (input : list record) : list record := sorry
def make_sort_rn (input : list record) : list record := sorry

-- sort
-- sort alphabetically in ascending order
-- no requirements on input
def sort (input : stream_of_strings) : stream_of_strings := 
  { records := make_sort input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [has_def_order] }

-- sort -r
-- sort alphabetically in descending order
-- no requirements on input
def sort_r (input : stream_of_strings) : stream_of_strings := 
  { records := make_sort_r input.records,
    column_types := input.column_types,
    per_line := input.per_line,
    bet_line := [has_r_order] }

-- sort -n
-- sort numerically in ascending order
-- helper checks that the first column has numeric type
def sort_n_helper : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := make_sort_n sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [has_n_order]}
| _ _ := none
def sort_n (input : stream_of_strings) : option stream_of_strings := 
  sort_n_helper input input.column_types

-- sort -rn
-- sort numerically in descending order
-- helper checks that the first column has numeric type
def sort_rn_helper : stream_of_strings → list type → option stream_of_strings 
| sos (type.num :: ts) := some {records := make_sort_rn sos.records,
                                column_types := sos.column_types,
                                per_line := sos.per_line,
                                bet_line := [has_rn_order]}
| _ _ := none
def sort_rn (input : stream_of_strings) : option stream_of_strings := 
  sort_n_helper input input.column_types

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

inductive is_in {α : Type} : α → list α → Prop
| intro_head (a : α) (as : list α) : is_in a (a::as)
| intro_rest (a b : α) (as : list α) : is_in a as → is_in a (b::as)

inductive no_duplicates {α : Type} : list α → Prop
| intro_base : no_duplicates list.nil
| intro_rest (a : α) (as : list α) : ¬(is_in a as) → no_duplicates as → no_duplicates (a::as)

theorem sort_then_uniq (input : stream_of_strings) : no_duplicates (sort (uniq input)).records 
  := sorry

end shell
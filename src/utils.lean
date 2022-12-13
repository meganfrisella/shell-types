
namespace utils

-- TODO: make more sophisticated (using ASCII values?)
def string_to_nat : string → nat
| "1" := 1
| "2" := 2
| "3" := 3
| "4" := 4
| "5" := 5
| "6" := 6
| "7" := 7
| _ := 0

def list_to_string {α : Type} [has_to_string α]: list α → string
| (s :: ss) := to_string s ++ list_to_string ss
| [] := ""

end utils
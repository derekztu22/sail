
let x : range(0, 255) = 42

let (y, z) = (20, 300000000000000000000000)

let (size as atom('size)) : {|32, 64|} = 32

$[sv_module { stdout = true }]
val print_endline = "print_endline" : string -> unit
val print = "print_endline" : string -> unit

$[sv_module { stdout = true }]
val print_int = "print_int" : (string, int) -> unit

val main : unit -> unit

function main () = {
  print_int("x = ", x);
  print_int("y = ", y);
  print_int("z = ", z);
  print_int("size = ", size);
}

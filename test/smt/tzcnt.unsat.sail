default Order dec

$include <prelude.sail>

val lzcnt = pure "count_trailing_zeros" : forall 'w. bits('w) -> range(0, 'w)

$property
function prop() -> bool = {
  let p1 = lzcnt(0x0) == 4;
  let p2 = lzcnt(0x00) == 8;
  let p3 = lzcnt(0x20) == 5;
  let p4 = lzcnt(0b10000000) == 7;
  let p5 = lzcnt(0b1) == 0;
  let p6 = lzcnt(0xF) == 0;
  p1 & p2 & p3 & p4 & p5 & p6
}

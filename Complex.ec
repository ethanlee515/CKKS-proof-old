require import AllCore.

type complex = [complex of real & real].
op re c = with c = complex r c => r.
op im c = with c = complex r c => c.
op from_real r = complex r 0%r.
abbrev (%c) = from_real.

clone include Ring.Field with
  type t <- complex,
  op zeror <- complex 0%r 0%r,
  op oner <- complex 1%r 0%r,
  op ( + ) <- fun c1 c2 => complex (re c1 + re c2) (im c1 + im c2),
  op [ - ] <- fun c => complex (-re c) (-im c),
  op ( * ) <- fun c1 c2 => complex (re c1 * re c2 - im c1 * im c2) (re c1 * im c2 + im c1 * re c2),
  op invr <- fun c =>
    let a = re c in
    let b = im c in
    let r = a * a + b * b in
    complex (a / r) (-b / r)
proof *.
realize addrA by smt().
realize addrC by smt().
realize add0r by smt().
realize addNr by smt().
realize oner_neq0 by smt().
realize mulrA by smt().
realize mulrC by smt().
realize mul1r by smt().
realize mulrDl by smt().
realize mulVr by move => c ne0_c /#.
realize unitP by smt().
realize unitout by smt().
realize mulf_eq0 by smt().

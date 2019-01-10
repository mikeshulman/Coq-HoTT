Require Import HoTT.Basics HoTT.Types.
Require Import DPath.

(* Squares *)

(* 
x00 ----pi0---- x01
 |               |
 |               |
p0i     ==>     p1i
 |               |
 |               |
x01-----pi1-----x11
 *)

(* We think of (and define) [Square p0i p1i pi0 pi1] as a
heterogeneous path from p0i to p1i over pi0 and pi1.  *)

Definition Square {A} {x00 x01 x10 x11 : A}
          (p0i : x00 = x01) (p1i : x10 = x11)
          (pi0 : x00 = x10) (pi1 : x01 = x11) : Type
  := dpath (fun xy:A*A => fst xy = snd xy) (path_prod' pi0 pi1) p0i p1i.

Definition sq_G1 {A} {x0 x1 : A} {p p' : x0 = x1} (q : p = p')
  : Square p p' 1 1
  := q.

Definition sq_id {A} {x0 x1 : A} (p : x0 = x1) : Square p p 1 1
  := sq_G1 (idpath p).

Definition sq_1G {A} {x0 x1 : A} {p p' : x0 = x1} (q : p = p')
  : Square 1 1 p p'.
Proof.
  destruct q, p; reflexivity.
Defined.

Definition sq_id' {A} {x0 x1 : A} (p : x0 = x1) : Square 1 1 p p
  := sq_1G (idpath p).

Definition sq_Cc {A} {x00 x01 x10 x11 x20 x21: A}
           {p0i : x00 = x01} {p1i : x10 = x11} {p2i : x20 = x21}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pj0 : x10 = x20} {pj1 : x11 = x21}
  (s01 : Square p0i p1i pi0 pi1) (s12 : Square p1i p2i pj0 pj1)
  : Square p0i p2i (pi0 @ pj0) (pi1 @ pj1).
Proof.
  destruct pi0, pi1, pj0, pj1; exact (s01 @ s12).
Defined.

Definition sq_Gccc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {p0i' : x00 = x01} (g0i : p0i' = p0i)
           (s : Square p0i p1i pi0 pi1)
  : Square p0i' p1i pi0 pi1.
Proof.
  destruct g0i; exact s.
Defined.

Definition sq_cGcc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {p1i' : x10 = x11} (g1i : p1i' = p1i)
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i' pi0 pi1.
Proof.
  destruct g1i; exact s.
Defined.

Definition sq_ccGc {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pi0' : x00 = x10} (gi0 : pi0 = pi0')
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i pi0' pi1.
Proof.
  destruct gi0; exact s.
Defined.

Definition sq_cccG {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           {pi1' : x01 = x11} (gi1 : pi1 = pi1')
           (s : Square p0i p1i pi0 pi1)
  : Square p0i p1i pi0 pi1'.
Proof.
  destruct gi1; exact s.
Defined.

Definition sq_tr {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (s : Square p0i p1i pi0 pi1)
  : Square pi0 pi1 p0i p1i.
Proof.
  destruct pi0, pi1, s, p0i; reflexivity.
Defined.

Definition sq_cC {A} {x00 x01 x10 x11 x02 x12: A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {p0j : x01 = x02} {p1j : x11 = x12}
           {pi0 : x00 = x10} {pi1 : x01 = x11} {pi2 : x02 = x12}
  (s01 : Square p0i p1i pi0 pi1) (s12 : Square p0j p1j pi1 pi2)
  : Square (p0i @ p0j) (p1i @ p1j) pi0 pi2
  := sq_tr (sq_Cc (sq_tr s01) (sq_tr s12)).

Definition sq_ap {A} {B} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (f : A -> B) (s : Square p0i p1i pi0 pi1)
  : Square (ap f p0i) (ap f p1i) (ap f pi0) (ap f pi1).
Proof.
  destruct pi0, pi1; exact (ap (ap f) s).
Defined.

Definition sq_nat {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : Square (ap f p) (ap f' p) (h x) (h y).
Proof.
  destruct p; apply sq_1G; reflexivity.
Defined.

Definition sq_sx {A B C} (f : A -> B) {g : B -> C} {k : A -> C}
           (h : g o f == k) {x y : A} (p : x = y)
  : Square (h x) (h y) (ap g (ap f p)) (ap k p).
Proof.
  destruct p; apply sq_G1; reflexivity.
Defined.

Definition sq_to_concat {A} {x00 x01 x10 x11 : A}
           {p0i : x00 = x01} {p1i : x10 = x11}
           {pi0 : x00 = x10} {pi1 : x01 = x11}
           (s : Square p0i p1i pi0 pi1)
  : p0i @ pi1 = pi0 @ p1i.
Proof.
  destruct pi0, pi1; cbn in *.
  destruct s, p0i; reflexivity.
Defined.

Definition DSquare {A : Type}
  (B : A -> Type)
  {a00 a01 a10 a11 : A}
  {p0i : a00 = a01} {p1i : a10 = a11} 
  {pi0 : a00 = a10} {pi1 : a01 = a11}
  (s : Square p0i p1i pi0 pi1)
  {b00 : B a00} {b01 : B a01}
  {b10 : B a10} {b11 : B a11}
  (q0i : dpath _ p0i b00 b01)
  (q1i : dpath _ p1i b10 b11)
  (qi0 : dpath _ pi0 b00 b10)
  (qi1 : dpath _ pi1 b01 b11)
  : Type.
Proof.
  destruct pi0, pi1, s, p0i.
  exact (Square q0i q1i qi0 qi1).
Defined.

Definition sq_prod {A B} 
  {a00 a01 a10 a11 : A}
  {p0i : a00 = a01} {p1i : a10 = a11} 
  {pi0 : a00 = a10} {pi1 : a01 = a11}
  (s : Square p0i p1i pi0 pi1)
  {b00 b01 b10 b11 : B}
  {q0i : b00 = b01} {q1i : b10 = b11} 
  {qi0 : b00 = b10} {qi1 : b01 = b11}
  (t : Square q0i q1i qi0 qi1)
  : Square (path_prod' p0i q0i) (path_prod' p1i q1i)
      (path_prod' pi0 qi0) (path_prod' pi1 qi1).
Proof.
  destruct pi1, pi0, s, p0i, qi1, qi0, t, q0i.
  reflexivity.
Defined.






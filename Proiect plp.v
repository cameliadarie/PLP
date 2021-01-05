Require Import PeanoNat.
Require Import Omega.

Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Set Nested Proofs Allowed.


Inductive AExp :=
| avar : string -> AExp
| aint : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
|aminus : AExp ->AExp->AExp
| amod : AExp -> AExp -> AExp.

Coercion aint : nat >-> AExp.
Coercion avar : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (aminus A B) (at level 60).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A /' B" := (adiv A B) (at level 58).
Notation "A %' B" := (amod A B) (at level 57).


Definition Env := string -> nat.

Definition env : Env :=
  fun x => 0.

Definition update (env : Env) (a : string) (val : nat) : Env :=
  fun x => if (eqb x a)
              then val
              else env x.

Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, aint n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> (sigma v)
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[ sigma ]=> n
| sub' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[ sigma ]=> n
| mul' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    negb(Nat.eqb i2 0) = true ->
    n = i1 / i2 ->
    a1 /' a2 =[ sigma ]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    negb(Nat.eqb i2 0) = true ->
    n = i1 mod i2 ->
    a1 %' a2 =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| blesseg:  AExp -> AExp -> BExp
| beg : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| bor : BExp -> BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "! A" := (bnot A) (at level 50).
Notation "A ==' B" := (beg A B) (at level 51 ).
Notation "A <<' B" := (blessthan A B) (at level 51).
Notation "A <=' B" := (blesseg A B) (at level 51).

Notation "A '&&'' B" := (band A B) (at level 55).
Notation "A '||'' B" := (bor A B) (at level 55).

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (i1 <? i2) ->
    a1 <<' a2 ={ sigma }=> b
| e_lesseg : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (i1 <=? i2) ->
    a1 <=' a2 ={ sigma }=> b
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (Nat.eqb i1 i2) ->
    a1 ==' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    bor b1 b2 ={ sigma }=> true
| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    bor b1 b2 ={ sigma }=> t
where "B ={ S }=> B'" := (beval B S B').

Inductive limbaj :=
| assignment : string -> AExp -> limbaj
| adecnull : string -> limbaj
|sequence : limbaj -> limbaj -> limbaj
| adec : string -> AExp -> limbaj
| ifthen : BExp -> limbaj -> limbaj
| ifthenelse : BExp -> limbaj -> limbaj -> limbaj
| whiledo : BExp -> limbaj -> limbaj
| fordo : limbaj -> BExp -> limbaj -> limbaj -> limbaj
| apointer : limbaj -> limbaj
| areferinta : AExp -> AExp -> limbaj
| switch : AExp -> limbaj-> limbaj
|case : AExp->AExp ->limbaj
| break: limbaj
|continue: limbaj.

Notation "X ::= A" := (assignment X A) (at level 40).
Notation "'declare*' A" := (adecnull A) (at level 40).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 85).
Notation "'declare' A =' B" := (adec A B) (at level 40).
Notation "'Iff' A 'Then' B" := (ifthen A B) (at level 85).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 85).
Notation "'While' '(' A ')' '(' B ')'" := (whiledo A B) (at level 85).
Notation "'For' '(' A ; B ; C ')' '(' D ')'" := (fordo A B C D) (at level 85).
Notation "A '=' '&' C  " := (areferinta A C) (at level 85, right associativity).
Notation "'bint''*' A " := (apointer A ) (at level 85, right associativity).
Notation "'break'" := (break) (at level 85).
Notation "'continue'" := (continue) (at level 85).
Notation "'switch' '(' A ')' '{'  'case'  B ':' C  '}'" := (switch A case B C) (at level 85).

 
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval : limbaj -> Env -> Env -> Prop :=
| e_intnull : forall v sigma sigma', 
    sigma' = (update sigma v 0) ->
    (declare* v) -{ sigma }-> sigma'
| e_intn : forall a b i sigma sigma', (* int "a" =' b *)
    b =[ sigma ]=> i ->
    sigma' = (update sigma a i) ->
    (declare a =' b) -{ sigma }-> sigma'
| e_assignment : forall x a i sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_ifthen_false : forall b s1 sigma,
    b ={ sigma }=> false ->
    (Iff b Then s1) -{ sigma }-> sigma
| e_ifthen_true : forall b s1 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (Iff b Then s1) -{ sigma }-> sigma1
| e_ifthenelse_false : forall b s1 s2 sigma sigma2,
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma2 ->
    (If b Then s1 Else s2) -{ sigma }-> sigma2
| e_ifthenelse_true : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (If b Then s1 Else s2) -{ sigma }-> sigma1
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    whiledo b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; whiledo b s) -{ sigma }-> sigma' ->
    whiledo b s -{ sigma }-> sigma'
| e_forfalse : forall e1 e2 e3 s sigma,
    e2 ={ sigma }=> false ->
    fordo e1 e2 e3 s -{ sigma }-> sigma
| e_fortrue : forall e1 e2 e3 s sigma sigma',
    e2 ={ sigma }=> true ->
    (e1 ;; whiledo e2 (s ;; e3)) -{ sigma }-> sigma' ->
    fordo e1 e2 e3 s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


Definition program :=
(
  declare "a" =' 0;;
  Iff ( "a" ==' 0) Then
    "a" ::=1 ;;
  While ("a" <=' 2)
  ( 
    "a" ::= ("a" +' 2)
  ) ;;
  declare* "i";;
break;;
continue;;

  For ("i" ::= 0 ; "i" <=' 1 ; "i" ::= ("i" +' 2))
  (
    "a" ::= ("a" +' 1)
  ) 

).


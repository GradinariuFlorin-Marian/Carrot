Require Import Strings.String.
Local Open Scope string_scope. 
Scheme Equality for string.
Require Import Coq.Strings.Byte.

(* Tipuri de date boolean/nat/string*)
Inductive boolv :=
  | errorB: boolv
  | boolV: bool -> boolv.

Inductive natv :=
  | errorNt: natv
  | natV: nat -> natv.

Inductive strv :=
  | errorS: strv
  | strV: string -> strv.

Coercion natV : nat >-> natv.
Coercion boolV : bool >-> boolv.
Coercion strV : string >-> strv.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : natv -> Result
  | res_bool :natv -> Result
  | res_str: strv -> Result.

Scheme Equality for Result.

Definition Env := nat -> Result.
Definition Env1 := string -> Result.
Definition Env2 := bool -> Result.

Definition env : Env := fun x => err_undecl.
Definition env1 : Env := fun x => err_undecl.
Definition env2 : Env := fun x => err_undecl.

Inductive Exp:=
  | bool: boolv -> Exp
  | boolt : Exp
  | boolf : Exp
  | nat: natv -> Exp
  | stri: strv -> Exp
  | variable: string -> Exp
  | add: Exp -> Exp -> Exp
  | sub: Exp -> Exp -> Exp
  | mul: Exp -> Exp -> Exp
  | div: Exp -> Exp -> Exp
  | mod: Exp -> Exp -> Exp
  | not: Exp -> Exp
  | and: Exp -> Exp -> Exp
  | or_b: Exp -> Exp -> Exp
  | lthan: Exp -> Exp -> Exp
  | ltaneq: Exp -> Exp -> Exp
  | greater: Exp-> Exp -> Exp
  | greatereq: Exp -> Exp -> Exp
  | eq: Exp -> Exp -> Exp
  | neq: Exp -> Exp -> Exp
  | conc: strv -> strv -> Exp
  | len: strv -> Exp
  | cmp: strv -> strv ->Exp.

Coercion bool : boolv >-> Exp.
Coercion nat: natv >-> Exp.
Coercion stri : strv >-> Exp.
Coercion variable : string >-> Exp.

Notation "C0 +\' C1" := (conc C0 C1) (at level 31, left associativity).
Notation " @' A  ":=(len A) (at level 30).
Notation " A ()' B":=(cmp A B) (at level 30).

Notation "A +' B" := (add A B)(at level 33, left associativity).
Notation "A -' B" := (sub A B)(at level 33, left associativity).
Notation "A *' B" := (mul A B)(at level 33, left associativity).
Notation "A /' B" := (div A B)(at level 31, left associativity).
Notation "A %' B" := (mod A B)(at level 31, left associativity).
Notation "! A" := (not A) (at level 30, right associativity).
Notation "A &&' B" := (and A B) (at level 33, left associativity).
Notation "A ||' B" := (or A B) (at level 32, left associativity).
Notation "A <' B" := (lthan A B) (at level 32, left associativity).
Notation "A <=' B" := (ltaneq A B) (at level 32, left associativity).
Notation "A >' B" := (greater A B) (at level 32, left associativity).
Notation "A >=' B" := (greatereq A B) (at level 32, left associativity).
Notation "A == B" := (eq A B) (at level 33, left associativity).
Notation "A != B" := (neq A B) (at level 33, left associativity).

Compute 1 +' 2.
Compute "x" -' 6.
Compute "andrei +\' are mere".
Compute !true.
Compute "text ()'  text".
Compute 1 != 5.
(*Operatii stringuri *)
Definition slength (strin : strv) : natv :=
  match strin with 
    | errorS => errorNt
    | strV  str=> length str
end.
Compute slength "text".

Definition plus_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV v1, natV v2 => natV (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : natv) :natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV n1, natV n2 => if Nat.ltb n1 n2
                        then errorNt
                        else natV (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV v1, natV v2 => natV (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | _, natV 0 => errorNt
    | natV v1, natV v2 => natV (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | _, natV 0 => errorNt
    | natV v1, natV v2 => natV (v1 - v2 * (Nat.div v1 v2))
    end.

Definition sconcat (str1 : strv) (str2 : strv) : strv :=
    match str1,str2 with 
    | errorS, _ => errorS
    | _, errorS => errorS
    | strV s1, strV s2 => s1 ++ s2
end.
Definition scmp (str1 : strv) (str2 : strv) : strv :=
    match str1,str2 with 
    | errorS, _ => errorS
    | _, errorS => errorS
    | strV s1 , strV s2 =>if (Nat.leb(length s1) (length s2))
                                then s2
                                else s1
end.
Compute scmp "andrei" "radu".
Compute sconcat "abc" "def".

Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 80).

Inductive Stmt :=
| nat_dec : string -> Exp -> Stmt
| bool_dec : string -> Exp -> Stmt
| string_dec : string -> string -> Stmt
| natass: string -> Exp -> Stmt
| boolass : string -> Exp -> Stmt
| stringass : string -> Exp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| while : Exp -> Stmt -> Stmt
| FOR : Stmt -> Exp -> Stmt -> Stmt
| read : string -> Stmt
| write : string -> Stmt.

Notation "A :n= B" := (natass A B)(at level 70).
Check "var" :n= "i" +' 10.

Notation "A :b= B" := (boolass A B)(at level 70).
Check "var1" :b= boolf.

Notation "A :s= B" := (stringass A B)(at level 70).
Check "var2" :s= "mama".

Notation "'Nat' A ::= B" := (nat_dec A B)(at level 70).
Check Nat "var" ::=10 .

Notation "'Bool' A ::= B" := (bool_dec A B)(at level 70).
Check Bool "var1" ::= boolf .

Notation "'String' A ::= B " := (string_dec A B)(at level 70).
Check String "var2" ::= "te" .

(*Operatiile de cin/cout *)
Notation "cin>> A ":=(read A) (at level 70).
Check cin>> "test".

Notation "cout<< A ":=(write A) (at level 70).
Check cout<< "test".
(* *)
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 71).
Notation "'If' B 'Then' S  'End'" := (ifthen B S) (at level 71).

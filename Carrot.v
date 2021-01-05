(* Pentru string *)
Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(* Tipuri de date boolean/int/string*)
Inductive natv :=
  | errorNt: natv
  | natV: nat -> natv.
Coercion natV : nat >-> natv.

Inductive boolv :=
  | errorB: boolv
  | boolV: bool -> boolv.
Coercion boolV : bool >-> boolv.

Inductive strv :=
  | errorS: strv
  | strV: string -> strv.
Coercion strV : string >-> strv.


Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : natv -> Result
  | res_bool :boolv -> Result
  | res_str: strv -> Result.

Scheme Equality for Result.

Definition Env := string -> Result.

Definition env : Env := fun x => err_undecl.
Definition env_notdecl : Env :=
    fun v => err_assign.

(*Verificarea existentei variabilei*)
Definition CheckVariable (a : Result) (b : Result) : bool :=
  match a with
  | err_undecl => match b with
                   | err_undecl => true
                   | _ => false
                   end
  | err_assign => match b with
                   | err_assign => true
                   | _ => false
                   end
  | res_nat n1 => match b with
                   | res_nat n2 => true
                   | _ => false
                   end
  | res_bool b1 => match b with
                   | res_bool b2 => true
                   | _ => false
                   end
  | res_str s1 => match b with
                   | res_str s2 => true
                   | _ => false
                   end
  | default => match b with
                   | default => true
                   | _ => false
                   end
end.

Definition update (env : Env) (s : string) (x : Result) : Env :=
  fun y => if (eqb y s)
              then 
              if (andb (CheckVariable (err_undecl) (env y)) (negb(CheckVariable (default) (x))))
              then err_undecl
              else
                if (andb (CheckVariable (err_undecl) (env y)) (CheckVariable (default) (x)))
                then default
                else
                  if (orb (CheckVariable (default) (env y)) (CheckVariable (x) (env y)))
                  then x
                  else err_assign
            else env y.
Check (env "x").

Inductive AExp:=
  | avar: string -> AExp
  | anum: natv -> AExp
  | aadd: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp
  | amax:  AExp -> AExp -> AExp
  | amin:   AExp -> AExp -> AExp.

Coercion anum : natv >-> AExp.
Coercion avar : string >-> AExp.
(*Notatii operatii tip nat *)
Notation "A +' B" := (aadd A B)(at level 33, left associativity).
Notation "A -' B" := (asub A B)(at level 33, left associativity).
Notation "A *' B" := (amul A B)(at level 33, left associativity).
Notation "A /' B" := (adiv A B)(at level 31, left associativity).
Notation "A %' B" := (amod A B)(at level 31, left associativity).
Notation "A []' B" := (amax A B)(at level 31, left associativity).
Notation "A ][' B" := (amin A B)(at level 31, left associativity).

Compute 5 +' 3.
Compute "x" -' 2.

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

Definition max_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV v1, natV v2 => if( Nat.leb v1  v2)
                                       then v2
                                       else v1
    end.

Compute max_ErrorNat 19 15.

Definition min_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV v1, natV v2 => if( Nat.leb v1  v2)
                                       then v1
                                       else v2
    end.

Compute min_ErrorNat 19 15.

(* Bool *)
Inductive BExp:=
  | bool: string -> BExp
  | berror: BExp
  | btrue: BExp
  | bfalse: BExp
  | bnot: BExp -> BExp
  | band: BExp -> BExp -> BExp
  | or: BExp -> BExp -> BExp
  | lthan: AExp -> AExp -> BExp
  | greater: AExp-> AExp -> BExp.

Coercion bool : string >-> BExp.

(*Notatii operatii tip boolean *)
Notation "! A" := (bnot A) (at level 30, right associativity).
Notation "A &&' B" := (band A B) (at level 33, left associativity).
Notation "A ||' B" := (or A B) (at level 32, left associativity).
Notation "A <' B" := (lthan A B) (at level 32, left associativity).
Notation "A >' B" := (greater A B) (at level 32, left associativity).

Definition ltthan_ErrorBool (n1 n2 : natv) : boolv :=
  match n1, n2 with
    | errorNt, _ => errorB
    | _, errorNt => errorB
    | natV v1, natV v2 =>  boolV (Nat.ltb v1 v2)
    end.

Definition ltgreater_ErrorBool (n1 n2 : natv) : boolv :=
  match n1, n2 with
    | _, errorNt => errorB
    | errorNt, _ => errorB
    | natV v1, natV v2 =>  boolV(Nat.ltb v1 v2)
    end.
Check( ltgreater_ErrorBool 5 6).

Definition not_ErrorBool (n :boolv) : boolv :=
  match n with
    | errorB => errorB
    | boolV v => boolV (negb v)
    end.

Definition and_ErrorBool (n1 n2 : boolv) : boolv :=
  match n1, n2 with
    | errorB, _ => errorB
    | _, errorB => errorB
    | boolV v1, boolV v2 =>  boolV (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : boolv) : boolv :=
  match n1, n2 with
    | errorB, _ => errorB
    | _, errorB => errorB
    | boolV v1, boolV v2 =>  boolV (orb v1 v2)
    end.

Inductive SExp:=
  | string_var: string -> SExp
  | string_error: strv -> SExp
  | snum: AExp -> SExp
  | sbool: BExp -> SExp
  | conc: strv -> strv -> SExp
  | len: strv -> SExp
  | cmp: strv -> strv -> SExp.
Coercion string_var : string >-> SExp.

(*Notatii operatii tip string *)
Notation "A +\' B" := (conc A B) (at level 31, left associativity).
Notation " @' A  ":=(len A) (at level 30).
Notation " A ()' B":=(cmp A B) (at level 30).

Compute "andrei +\' are mere".

Definition slength (strin : strv) : natv :=
  match strin with 
    | errorS => errorNt
    | strV  str=> length str
end.

Compute slength "text5".

Definition sconcat (str1 : strv) (str2 : strv) : strv :=
    match str1,str2 with 
    | errorS, _ => errorS
    | _, errorS => errorS
    | strV s1, strV s2 => strV( s1 ++ s2)
end.

Compute sconcat "Ana " "are mere".

Definition scmp (str1 : strv) (str2 : strv) : strv :=
    match str1,str2 with 
    | errorS, _ => errorS
    | _, errorS => errorS
    | strV s1 , strV s2 =>if (Nat.leb(length s1) (length s2))
                                then s2
                                else s1
end.

Inductive Stmt :=
| nat_dec : string -> AExp -> Stmt
| bool_dec : string -> BExp -> Stmt
| string_dec : string -> SExp -> Stmt
| natass: string -> AExp -> Stmt
| boolass : string -> BExp -> Stmt
| stringass : string -> SExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| FOR : Stmt -> BExp -> Stmt -> Stmt
| comm: Stmt -> Stmt
| read : SExp -> Stmt
| write : string -> Stmt.

(*Notatii Statement *)
Notation "A :n= B" := (natass A B)(at level 70).
Check "var" :n= "i" +' 10.

Notation "A :b= B" := (boolass A B)(at level 70).
Check "var1" :b= bfalse.

Notation "A :s= B" := (stringass A B)(at level 70).
Check "var2" :s= "mama".

Notation "'Nat' A ::= B" := (nat_dec A B)(at level 70).
Check Nat "var" ::=10 .

Notation "'Bool' A ::= B" := (bool_dec A B)(at level 70).
Check Bool "var1" ::= btrue .

Notation "'String' A ::= B " := (string_dec A B)(at level 70).
Check String "var2" ::= "te" .

Notation "cin>> A ":=(write A) (at level 70).
Check cin>> "A".

Notation "cout<< A ":=(read A) (at level 70).
Check cout<< "A".

Notation "'If' B 'Then' S  'End'" := (ifthen B S) (at level 71).

Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 71).

Notation "'While' ( A ) B" := (while A B)(at level 71).

Notation "A ;; B" := (sequence A B) (at level 71).

Notation "'For' ( A \ B \ C ) D " := (A ;; while B ( D ;; C ))(at level 71).
(*Comentarii *)
Notation " ||* a *|| " := (comm a ) (at level 72).

Check ( Nat "n" ::= 10 ;; String "y" ::= "ab" ).
Check env "v1".
Check (4 *' 9).

(* Small step pentru operatii recursive *)
Fixpoint aeval_fun (a : AExp) (env : Env) : natv :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => errorNt
                end
  | anum v => v
  | aadd a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | asub a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amax a1 a2 => (max_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amin a1 a2 => (min_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.

Reserved Notation "A =[ S ]=> N" (at level 60). 
(* Big step pentru operatii cu nat *)
Inductive aeval : AExp -> Env -> natv -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => errorNt
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
| max : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (max_ErrorNat i1 i2) ->
    a1 []' a2 =[sigma]=> n
| min : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (min_ErrorNat i1 i2) ->
    a1 ][' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Example substract_error : 1 -' 5 =[ env ]=> errorNt.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example division_error : 3 /' 0 =[ env ]=> errorNt.
Proof.
  eapply division.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example modulo_error : 3 %' 0 =[ env ]=> errorNt.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.
Check ( 5 ][' 7).

(*Small step *)
Fixpoint beval_fun (a : BExp) (envnat : Env) : boolv :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => errorB
  | bool v => match (env v) with
               | res_bool n => n
               | _ => errorB
               end
  | lthan a1 a2 => (ltthan_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | or b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | greater a1 a2 => (ltgreater_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  end.
Reserved Notation "B ={ S }=> B'" (at level 70).
(* Big step pentru Boolean *)
Inductive beval : BExp -> Env -> boolv -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> errorB
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bool v ={ sigma }=>  match (sigma v) with
                                                | res_bool x => x
                                                | _ => errorB
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (ltthan_ErrorBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    ! a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

Example boolean_operation : bnot (100 <' "n") ={ env }=> errorB.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Reserved Notation "S --{ sigm }-> sigm'" (at level 80).
(* Big step pentru Statements *)
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   sigma' = (update sigma x (res_nat i)) ->
   (x :n= a) --{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) --{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   sigma' = (update sigma x (res_bool i)) ->
   (x :b= a) --{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) --{ sigma }-> sigma'
| e_str_decl: forall a i x sigma sigma',
   sigma' = (update sigma x (res_str i)) ->
   (x :s= a) --{ sigma }-> sigma'
| e_str_assign: forall a i x sigma sigma',
    sigma' = (update sigma x (res_str i)) ->
    (x :s= a) --{ sigma }-> sigma'  
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 --{ sigma }-> sigma1 ->
    s2 --{ sigma1 }-> sigma2 ->
    (s1 ;; s2) --{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s --{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 --{ sigma }-> sigma' ->
    ifthenelse b s1 s2 --{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 --{ sigma }-> sigma' ->
    ifthenelse b s1 s2 --{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s --{ sigma }-> sigma
| e_com : forall s sigma1 sigma2 ,
    ||* s *|| --{ sigma1 }-> sigma2
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) --{ sigma }-> sigma' ->
    while b s --{ sigma }-> sigma'
where "sm --{ sigm }-> sigm'" := (eval sm sigm sigm').

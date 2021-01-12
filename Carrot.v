(* Pentru string *)
Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(* Tipuri de date boolean/int/string*)
Inductive natv :=
  | errorNt: natv
  | natV: nat -> natv.

Inductive boolv :=
  | errorB: boolv
  | boolV: bool -> boolv.

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
Compute CheckVariable (res_nat 15) (res_nat 25).

Definition update (env : Env) ( s: string ) ( v : Result ) : Env :=
fun y =>
 if(string_beq s y) then 
     if ( andb( CheckVariable (env y) err_undecl) true )
                     then  v
         else if (andb( CheckVariable (env y) v) true ) then v else err_assign 
      else (env y).
Check (env "x").
Notation "S [ V /' X ]" := (update S X V) ( at level 0).
Check (update env "x" (res_nat 5)).
Inductive SExp:=
  | string_var: string -> SExp
  | string_error: strv ->SExp
  | conc: strv -> strv -> SExp 
  | cmp: strv -> strv -> SExp.
Coercion string_var : string >-> SExp.

Inductive AExp:=
  | avar: string -> AExp
  | anum: natv -> AExp
  | aadd: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp
  | amax:  AExp -> AExp -> AExp
  | amin:   AExp -> AExp -> AExp
 | len: strv -> AExp.

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
Compute plus_ErrorNat (natV 9) (natV 15).
Definition sub_ErrorNat (n1 n2 : natv) :natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV n1, natV n2 => if Nat.ltb n1 n2
                        then errorNt
                        else natV (n1 - n2)
    end.
Compute sub_ErrorNat (natV 8) (natV 3).
Definition mul_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | natV v1, natV v2 => natV (v1 * v2)
    end.
Compute mul_ErrorNat (natV 2) (natV 5).
Definition div_ErrorNat (n1 n2 : natv) : natv :=
  match n1, n2 with
    | errorNt, _ => errorNt
    | _, errorNt => errorNt
    | _, natV 0 => errorNt
    | natV v1, natV v2 => natV (Nat.div v1 v2)
    end.
Compute div_ErrorNat (natV 10) (natV 2).
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

Definition conv (st: strv) : string := 
  match st with
  | errorS => ""
  | strV s' => s'
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
| nat_dec : string  -> Stmt
| bool_dec : string  -> Stmt
| string_dec : string -> Stmt
| natass: string -> AExp -> Stmt
| boolass : string -> BExp -> Stmt
| stringass : string -> SExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| FOR : Stmt -> BExp -> Stmt -> Stmt
| comm: string -> Stmt
| read : string -> Stmt
| write : SExp -> Stmt.

(*Notatii Statement *)
Notation "A :n= B" := (natass A B)(at level 70).
Check "var" :n= "i" +' 10.

Notation "A :b= B" := (boolass A B)(at level 70).
Check "var1" :b= bfalse.

Notation "A :s= B" := (stringass A B)(at level 70).
Check "var2" :s= "mama".

Notation "'Nat' A " := (nat_dec A)(at level 70).
Check Nat "var" .

Notation "'Bool' A " := (bool_dec A)(at level 70).
Check Bool "var1" .

Notation "'Str' A " := (string_dec A)(at level 70).
Check Str "var2" .

Notation "\cin>> A ":=(write A) (at level 70).
Check \cin>>( "A").

Notation "\cout<<(' A )":=(read A) (at level 70).
Check \cout<<(' "A").

Notation "'If' B 'then' S  'end" := (ifthen B S) (at level 71).

Notation "'If' B 'then' S1 'else' S2 'end" := (ifthenelse B S1 S2) (at level 71).

Notation "'While' ( A ) B" := (while A B)(at level 71).

Notation "A ;; B" := (sequence A B) (at level 71).

Notation "'For' ( A \ B \ C ) D " := (A ;; while B ( D ;; C ))(at level 71).
(*Comentarii *)
Notation " ||* a *|| " := (comm a ) (at level 72).

Check ( Nat "n"  ;; Str "y" ).
Check env "v1".
Check (4 *' 9).
Reserved Notation "B ~{ S }~> B'" (at level 70).
Inductive seval: SExp -> Env -> strv -> Prop :=
| s_var: forall v sigma, string_var v ~{ sigma }~>  match (sigma v) with
                                              | res_str x => x
                                              | _ => errorS
                                              end
| s_error: forall n sigma, string_error n ~{ sigma }~> n
| s_cat: forall a1 a2 i1 i2 sigma b,
    a1 ~{  sigma }~> i1 ->
    a2 ~{  sigma }~> i2 ->
    b = (sconcat i1 i2) ->
    i1 +\' i2 ~{ sigma }~> b
| s_cmp: forall a1 a2 i1 i2 sigma b,
    a1 ~{  sigma }~> i1 ->
    a2 ~{  sigma }~> i2 ->
    b = (scmp i1 i2) ->
    i1 ()' i2 ~{ sigma }~> b
where "B ~{ S }~> B'" := (seval B S B').

Reserved Notation "A =[ S ]=> N" (at level 60). 
(* Big step pentru operatii cu nat *)
Inductive aeval : AExp -> Env -> natv -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => errorNt
                                              end
| add : forall a1 a2 i1 i2 n sigma,
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
(*| len : forall a1 i1  sigma n,
    a1 =  (slength i1) ->
    @' a1 =[sigma]=> n
*)

where "a =[ sigma ]=> n" := (aeval a sigma n).

Check ( 5 ][' 7).

Reserved Notation "B -{ S }-> B'" (at level 70).
(* Big step pentru Boolean *)
Inductive beval : BExp -> Env -> boolv -> Prop :=
| b_error: forall sigma, berror  -{ sigma }-> errorB
| b_true : forall sigma, btrue -{ sigma }-> true
| b_false : forall sigma, bfalse -{ sigma }-> false
| b_var : forall v sigma, bool v -{ sigma }->  match (sigma v) with
                                                | res_bool x => x
                                                | _ => errorB
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (ltthan_ErrorBool i1 i2) ->
    a1 <' a2 -{ sigma }-> b
| b_greater : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (ltgreater_ErrorBool i1 i2) ->
    a1 >' a2 -{ sigma }-> b
| b_not : forall a1 i1 sigma b,
    a1 -{ sigma }-> i1 ->
    b = (not_ErrorBool i1) ->
    ! a1 -{ sigma }-> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 -{ sigma }-> i1 ->
    a2 -{ sigma }-> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 &&' a2) -{ sigma }-> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 -{ sigma }-> i1 ->
    a2 -{ sigma }-> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 ||' a2) -{ sigma }-> b 
where "B -{ S }-> B'" := (beval B S B').

Reserved Notation "S --{ sigm }-> sigm'" (at level 80).
(* Big step pentru Statements *)
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall x sigma sigma',
   sigma' = update sigma x (res_nat 0) ->
   (Nat x) --{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->  
    sigma' = update sigma x (res_nat i) ->
    (x :n= a) --{ sigma }-> sigma'
| e_bool_decl: forall x sigma sigma',
   sigma' = update sigma x (res_bool true) ->
   (Bool x) --{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a -{ sigma }-> i ->  
    sigma' = update sigma x (res_bool i) ->
    (x :b= a) --{ sigma }-> sigma'
| e_str_decl: forall x sigma sigma',
   sigma' = update sigma x (res_str "") ->
   (Str x) --{ sigma }-> sigma'
| e_str_assign: forall a i x sigma sigma',
    a ~{ sigma }~> i ->  
    sigma' = (update sigma x (res_str i)) ->
    (x :s= a) --{ sigma }-> sigma'  
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 --{ sigma }-> sigma1 ->
    s2 --{ sigma1 }-> sigma2 ->
    (s1 ;; s2) --{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s --{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b -{ sigma }-> true ->
    s1 --{ sigma }-> sigma' ->
    ifthenelse b s1 s2 --{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b -{ sigma }-> false ->
    s2 --{ sigma }-> sigma' ->
    ifthenelse b s1 s2 --{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b -{ sigma }-> false ->
    while b s --{ sigma }-> sigma
| e_com : forall s sigma1 sigma2 ,
    ||* s *|| --{ sigma1 }-> sigma2
| e_whiletrue : forall b s sigma sigma',
    b -{ sigma }-> true ->
    (s ;; while b s) --{ sigma }-> sigma' ->
    while b s --{ sigma }-> sigma'
where "sm --{ sigm }-> sigm'" := (eval sm sigm sigm').

Hint Constructors aeval : my_hints.
Hint Constructors beval : my_hints.
Hint Constructors eval : my_hints.
Hint Unfold update : my_hints.

(* Exemple *)
Check ( 9 <' ("x" /' 5) ) .
Check (12 %' 3).
Check( "@' text").
Check(" andrei () gelu").

Example dec := 
 Bool "a" ;;
 Bool "b" ;;
 "a" :b= btrue;;
 "b" :b= bfalse.
Example dec_ev :
  exists state, dec --{ env }-> state.
Proof.
eexists.
unfold dec.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_bool_decl.
reflexivity.
eapply e_bool_decl.
reflexivity.
eapply e_bool_assign.
eapply b_true.
reflexivity.
eapply e_bool_assign.
eapply b_false.
reflexivity.
Qed.

Example dec2 := 
 Str "a" ;;
 Str "b" ;;
 "a" :s= "test1";;
 "b" :s= " test2".
Example dec2_ev :
  exists state, dec2 --{ env }-> state.
Proof.
eexists.
unfold dec.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_str_decl.
reflexivity.
eapply e_str_decl.
reflexivity.
eapply e_str_assign.
eapply s_var.
reflexivity.
eapply e_str_assign.
eapply s_var.
reflexivity.
Qed.
Example dec3 := 
 Str "a" ;;
 Str "b" ;;
 "a" :s= "test1";;
 "b" :s= " test2" ;;
  Str "c";;
 "c" :s= "a" +\' "b".
Example dec3_ev :
  exists state, dec3 --{ env }-> state.
Proof.
eexists.
unfold dec.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_str_decl.
reflexivity.
eapply e_str_decl.
reflexivity.
eapply e_str_assign.
eapply s_var.
reflexivity.
eapply e_str_assign.
eapply s_var.
reflexivity.
eapply e_str_decl.
reflexivity.
eapply e_str_assign.
eapply s_cat.
eapply s_error.
simpl.
eapply s_error.
simpl.
reflexivity.
reflexivity.
Qed.

Example ex1 : bnot (100 <' "n") -{ env }-> errorB.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Example ex2 : bnot (100 <' ("n" /' 0)) -{ env }-> errorB.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply division.
    * eapply var.
    * eapply const.
    * simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Example ex3 : 1 -' 5 =[ env ]=> errorNt.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex4 : 3 /' 0 =[ env ]=> errorNt.
Proof.
  eapply division.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex5 : 3 %' 0 =[ env ]=> errorNt.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex6 : 9 <' 12 -{ env }-> true .
eapply b_lessthan.
eapply const.
eapply const.
simpl.
reflexivity.
Qed.

Example ex7 : 12 +' 3 =[ env ]=>15.
Proof. 
eapply add.
eapply const. 
eapply const.
simpl.
reflexivity.
Qed.

Example ex8 : 12 +' 3 =[ env ]=>15.
Proof. 
eapply add.
eapply const. 
eapply const.
simpl.
reflexivity.
Qed.

Example ex9 : "a" =[ env ]=> errorNt.
Proof.
  eapply var.
Qed.
Example ex10 : "x" *' "x" =[update env "x" (res_nat 10)]=> 100.
Proof.
  eapply times.
   eauto.
  eapply var.
  eapply var.
  simpl.
  reflexivity.
Qed.

Example ex11 : btrue &&' btrue -{ env }-> true .
eapply b_and.
eapply b_true.
eapply b_true.
simpl.
reflexivity.
Qed.

Example ex13 := 
 Nat "a" ;;
 Nat "b" ;;
 Nat "s";;
 "a" :n= 5;;
 "b" :n=3;;
 "s" :n= "a" +' "b".

Example ex13_res :
  exists state, ex13 --{ env }-> state /\ state "s" = res_nat 8.
Proof.
eexists.
split.
unfold ex13.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_nat_decl.
reflexivity.
eapply e_nat_decl.
reflexivity.
eapply e_nat_decl.
reflexivity.
eapply e_nat_assign.
eapply const.
eauto.
eapply e_nat_assign.
eapply const.
reflexivity.
eapply e_nat_assign.
eapply add.
eauto.
eapply var.
eapply var.
simpl.
reflexivity.
reflexivity.
eauto.
Qed.

Example ex14 := 
 Nat "a"  ;;
 Nat "b"  ;;
 Nat "s" ;;
 "a" :n=4 ;;
 "b" :n=4 ;;
while ( "a" <' 6 )  
( "s" :n= ("s" +' 20) ;;
    "a" :n="a" +' 1 
    ).


Example ex14_ev :
  exists state, ex14 --{ env }-> state /\ state "s" =res_nat 40.
Proof.
eexists.
split.
unfold ex14.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_nat_decl.
eauto.
eapply e_nat_decl.
eauto.
eapply e_nat_decl.
eauto.
eapply e_nat_assign.
eauto.
eapply const.
eauto.
eapply e_nat_assign.
eauto.
eapply const.
eauto.
eapply e_whiletrue.
eapply b_lessthan.
eapply var.
eapply const.
reflexivity.
eapply e_seq.
eapply e_seq.
eapply e_nat_assign.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_nat_assign.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_whiletrue.
eapply b_lessthan.
eapply var.
eapply const.
reflexivity.
eapply e_seq.
eapply e_seq.
eapply e_nat_assign.
eapply add.
eapply var.
eapply const.
simpl.
reflexivity.
reflexivity.
eapply e_nat_assign.
eapply add.
eapply var.
eapply const.
reflexivity.
eauto.
eapply e_whilefalse.
eapply b_lessthan.
eapply var.
eapply const.
reflexivity.
simpl.
reflexivity.
Qed.

Example ex15 := 
 Nat "a"  ;;
 Nat "b"  ;;
 "a" :n=4 ;;
 "b" :n=4 ;;
||* "Acesta este un comentariu" *|| ;;
  If ( "b" <' 5) then
 "a" :n=8
  'end.
Example ex15_ev :
  exists state, ex15 --{ env }-> state.
Proof.
eexists.
unfold ex15.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_seq.
eapply e_nat_decl.
eauto.
eapply e_nat_decl.
eauto.
eapply e_nat_assign.
eauto.
eapply const.
eauto.
eapply e_nat_assign.
eauto.
eapply const.
eauto.
eapply e_seq.
eapply e_com.
eapply e_if_then.
Qed.

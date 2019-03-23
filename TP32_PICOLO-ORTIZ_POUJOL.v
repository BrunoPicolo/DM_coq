(* Bruno PICOLO ORTIZ Elyan POUJOL *)

Require Import Bool.
Require Import List.
Import ListNotations.
Set Implicit Arguments.

(* Ecriture de la spécification *)

Module Type TABLE.
Parameter Key: Type.
Parameter Val: Type.
Parameter table: Type.
Parameter empty: table.
Parameter put: table -> Key -> Val -> table.
Parameter get: table -> Key -> Val -> Val.
Parameter member: table -> Key -> bool.
Axiom get_empty: forall key def, get empty key def = def.
Axiom get_put_eq: forall key val def t, get (put t key val) key def = val.
Axiom get_put_neq: forall key1 key2 val def t,
key1<>key2 -> get (put t key1 val) key2 def = get t key2 def.
Axiom empty_mem: forall key, member empty key = false.
Axiom mem_put_eq: forall key val t, member (put t key val) key = true.
Axiom mem_put_neq: forall key1 key2 val t,
key1<>key2 -> member (put t key1 val) key2 = member t key2.
End TABLE.

Require Import Ascii. (* pour utiliser des caractères *)
Module Test(T:TABLE with Definition Key:=list ascii with Definition Val:=nat).
  Local Open Scope char_scope. (* pour pouvoir écrire "a" *)
  Definition test (k: T.Key) (v:T.Val) := 
    let t1 := T.empty in
    let t2 := T.put t1 k v in
    if T.member t2 k then 
      T.get t2 k v 
    else 
      let t2 := T.put t2 k v in v.
End Test.

(* Implémentation de la spécification *)



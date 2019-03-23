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

Module Type ALPHA.
  Parameter lettre: Type.
  Parameter eq: forall (x y:lettre), {x=y}+{x<>y}.
End ALPHA.

Module Type TYPE.
  Parameter t: Type.
End TYPE.

Module Trie (A:ALPHA) (T:TYPE) <:
  TABLE with Definition Key := list A.lettre with Definition Val := T.t.
    Definition Key := list A.lettre.
    Definition Val := T.t.
    Inductive trie :=
        Leaf (val: option Val)
      | Node (val: option Val) (reste: A.lettre -> trie).
    Definition table := trie.
    Definition empty := Leaf None.
    Definition isDefined T (v: option T) := (* teste si v <> None *)
      match v with
          None => false
        | _ => true
      end.
    Definition getValue T (v: option T) def := (* valeur dans Some, def sinon *)
      match v with
          None => def
        | Some u => u
      end.

    Fixpoint put t key val :=
      match key with
        | []    => failwith "Cle vide"
        | e::[] =>
            match t with
              | Leaf _   => Leaf (Some val)
              | Node _ r => Node (Some val, r)
            end
        | e::l  =>
            match t with
              | Leaf x   => Node x (fun c -> if A.eq e c then Leaf (Some val) else Leaf None)
              | Node x r => (* TODO *)
            end
      end.

    Fixpoint get t key val :=
      match key with
        | []    => failwith "Cle vide"
        | e::[] =>
            match t with
              | Leaf None
              | Node None _     => val
              | Leaf (Some x)
              | Node (Some x) _ => x
            end
        | e::l  =>
            match t with
              | Leaf _   => val
              | Node _ r => get (r e) l
            end
      end.

    Fixpoint member t key :=
      match key with
        | []    => failwith "Cle vide"
        | e::[] =>
            match t with
              | Leaf None
              | Node None _     => false
              | Leaf (Some _)
              | Node (Some _) _ => true
            end
        | e::l  =>
            match t with
              | Leaf _   => false
              | Node _ r => member (r e) l
            end
      end.

    Theorem get_empty: forall key def, get empty key def = def.
    Admitted.
    Theorem get_put_eq: forall key val def t, get (put t key val) key def = val.
    Admitted.
    Theorem get_put_neq: forall key1 key2 val def t,
    key1<>key2 -> get (put t key1 val) key2 def = get t key2 def.
    Admitted.
    Theorem empty_mem: forall key, member empty key = false.
    Admitted.
    Theorem mem_put_eq: forall key val t, member (put t key val) key = true.
    Admitted.
    Theorem mem_put_neq: forall key1 key2 val t,
      key1<>key2 -> member (put t key1 val) key2 = member t key2.
    Admitted.
End trie.

Inductive option T :=
  Some (valeur:T)
  | None.


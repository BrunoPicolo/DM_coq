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
  Definition test :=
    let t := T.put T.empty ["a"; "b"; "c"] 10 in
    if T.member t ["a"; "b"; "c"] then
      T.get t ["a"; "b"; "c"] 0
    else
      0.
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
      match t with
        | Leaf v =>
            match key with
              | [] => Leaf (Some val)
              | e::k =>
                  let t' := put (Leaf None) k val in
                  Node v ( fun x => if A.eq x e then t' else (Leaf None))
            end
        | Node v r =>
            match key with
              | [] => Node (Some val) r
              | e::k =>
                  let t' := put (r e) k val in
                  Node v (fun x => if A.eq x e then t' else r e)
            end
      end.

    Fixpoint get t key val :=
      match t with
        | Leaf v =>
            match key with
              | [] => getValue v val
              | e::k => val
            end
        | Node v r =>
            match key with
              | [] => getValue v val
              | e::k => get (r e) k val
            end
      end.

    Fixpoint member t key :=
      match key with
      | [] =>
          match t with
            | Leaf None
            | Node None _ => false
            | _ => true
          end
      | e::k =>
          match t with
            | Leaf _=> false
            | Node _ r => member (r e) k
          end
      end.


    Theorem empty_mem: forall key, member empty key = false.
    Proof.
    destruct key; try tauto.
    Qed.
    Print empty_mem.

    Theorem get_empty: forall key def, get empty key def = def.
    Proof.
    destruct key; try tauto. 
    Qed.
    Print get_empty.

    Theorem mem_put_eq: forall key val t, member (put t key val) key = true.
    Proof.
    induction key.
    destruct t; try tauto.
    destruct t; try tauto.
    simpl.
    destruct A.eq; try tauto.
    rewrite IHkey. auto.
    simpl.
    destruct A.eq; try tauto.
    rewrite IHkey. auto.
    Qed.

    Theorem get_put_eq: forall key val def t, get (put t key val) key def = val.
    Proof.
    induction key. 
    destruct t; try tauto.
    destruct t; try tauto.
    simpl.
    destruct A.eq; try tauto.
    rewrite IHkey; try tauto.
    simpl.
    destruct A.eq; try tauto.
    rewrite IHkey; try tauto.
    Qed.

    Theorem mem_put_neq: forall key1 key2 val t,
      key1<>key2 -> member (put t key1 val) key2 = member t key2.
    Proof.
    induction key1.
    destruct key2; try tauto.
    destruct t; try tauto.
    simpl.
    destruct t; try tauto.
    destruct val0; try tauto.
    simpl.
    destruct key2; try tauto.
    destruct A.eq; try tauto.
    intros.
    rewrite IHkey1.
    apply empty_mem.
    Admitted.


     Theorem get_put_neq: forall key1 key2 val def t,
    key1<>key2 -> get (put t key1 val) key2 def = get t key2 def.
    Proof.
    induction key1.
    destruct t; try tauto.
    simpl.
    intros.
    destruct key2; try tauto.
    intros.
    destruct key2; try tauto.
    intros.
    destruct t; try tauto.
    simpl.
    destruct key2; try tauto.
    destruct A.eq; try tauto.
    rewrite IHkey1.
    apply get_empty.
    intro.
    Admitted.
End Trie.

Inductive option T :=
  Some (valeur: T)
  | None.


Module StrK.
  Definition lettre := ascii.
  Definition eq := ascii_dec.
End StrK.

Module NatV.
  Definition t := nat.
End NatV.

Module TrieStrNat := Trie StrK NatV.
Module TestTrieStrNat := Test TrieStrNat.

Eval compute in TestTrieStrNat.test.

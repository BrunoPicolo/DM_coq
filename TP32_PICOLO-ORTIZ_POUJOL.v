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

(* Fixpoint put t key val :=
match t with 
| Leaf _   => 
    match key with
    | [] => Leaf (Somme val)
| Node x r => *)

    Fixpoint put t key val :=
      match key with
        | []    =>
            match t with
              | Leaf _ => Leaf (Some val)
              | Node _ r => Node (Some val) r
            end
        | e::[] =>
            match t with
              | Leaf x   => Node x (fun c => if A.eq e c then Leaf (Some val) else Leaf None)
              | Node x r => Node x (fun c => if A.eq e c then Leaf (Some val) else r c)
            end
        | e::l  =>
            match t with
              | Leaf x   =>
                  let t' := put (Leaf None) l val in
                  Node x (fun c => if A.eq e c then t' else Leaf None)
              | Node x r =>
                  let t' := put (r e) l val in
                  Node x (fun c => if A.eq e c then t' else r c)
            end
      end.

    Fixpoint get t key val :=
      match key with
        | []    => val (* cle vide, on retourne la valeur alternative *)
        | e::[] =>
            match t with
              | Leaf _ => val
              | Node _ r =>
                  match r e with
                    | Leaf (Some x)
                    | Node (Some x) _ => x
                    | Leaf None
                    | Node None _     => val
                  end
            end
        | e::l  =>
            match t with
              | Leaf _   => val
              | Node _ r => get (r e) l val
            end
      end.

    Fixpoint member t key :=
      match key, t with
        | [], Leaf (Some _) => true
        | _, Leaf _ => false
        | [], Node (Some _) _ => true
        | [], Node None _     => false
        | e::[], Node _ r =>
            match r e with
              | Leaf (Some x)
              | Node (Some x) _ => true
              | _               => false
            end
        | e::l, Node _ r => member (r e) l
      end.

    Theorem empty_mem: forall key, member empty key = false.
    Proof.
    destruct key; try tauto.
    simpl.
    destruct key; try tauto.
    Qed.

    (* Lemma put_empty_key: forall val t, put t [] val = t.
    Proof.
    auto.
    Qed. *)

    Theorem mem_put_eq: forall key val t, member (put t key val) key = true.
    Proof.
    induction key.
    destruct t; try tauto.
    destruct (A.eq a a).
    Admitted.

    Theorem get_empty: forall key def, get empty key def = def.
    destruct key; try tauto.
    destruct key; try tauto.
    Qed.

    Theorem mem_put_neq: forall key1 key2 val t,
      key1<>key2 -> member (put t key1 val) key2 = member t key2.
    induction key1.
    destruct key2; try tauto.
    destruct t.
    destruct val0.
    reflexivity.
    reflexivity.
    reflexivity.
    destruct (A.eq a a).
    Admitted.

    Theorem get_put_eq: forall key val def t, get (put t key val) key def = val.
    Proof.
    induction key. 
    destruct t.    
    simpl. 
    (*Destruction de l'égalité*)
    (*utiliser rewrite*)
    Admitted.

    Theorem get_put_neq: forall key1 key2 val def t,
    key1<>key2 -> get (put t key1 val) key2 def = get t key2 def.
    Proof.
    induction key1.
    destruct key2.
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

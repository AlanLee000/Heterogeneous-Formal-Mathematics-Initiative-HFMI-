From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryStage2.
Require Import FormalSystemFactoryBindingAPI.
Require Import FormalSystemFactoryRuleAPI.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module S2 := FormalSystemFactoryStage2.FormalSystemFactoryStage2.
Module B := FormalSystemFactoryBindingAPI.FormalSystemFactoryBindingAPI.
Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.

Module FormalSystemFactoryStructuralCodec.

Inductive code : Type :=
| CAtom : nat -> code
| CNode : nat -> list code -> code.

Record StructuralCodec (A : Type) := {
  encode_code : A -> code;
  decode_code : code -> option A;
  decode_encode_code :
    forall a, decode_code (encode_code a) = Some a
}.

Fixpoint decode_code_list {A : Type}
         (decode : code -> option A) (cs : list code) : option (list A) :=
  match cs with
  | [] => Some []
  | c :: rest =>
      match decode c, decode_code_list decode rest with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.

Definition encode_code_list {A : Type}
           (encode : A -> code) (xs : list A) : code :=
  CNode 0 (map encode xs).

Definition decode_code_list_node {A : Type}
           (decode : code -> option A) (c : code) : option (list A) :=
  match c with
  | CNode 0 cs => decode_code_list decode cs
  | _ => None
  end.

Lemma decode_code_list_map :
  forall (A : Type) (encode : A -> code) (decode : code -> option A),
    (forall a, decode (encode a) = Some a) ->
    forall xs,
      decode_code_list decode (map encode xs) = Some xs.
Proof.
  intros A encode decode H xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite H, IH; reflexivity.
Qed.

Lemma decode_code_list_node_encode :
  forall (A : Type) (encode : A -> code) (decode : code -> option A),
    (forall a, decode (encode a) = Some a) ->
    forall xs,
      decode_code_list_node decode (encode_code_list encode xs) = Some xs.
Proof.
  intros A encode decode H xs.
  unfold decode_code_list_node, encode_code_list.
  apply decode_code_list_map.
  exact H.
Qed.

Definition nat_structural_codec : StructuralCodec nat.
Proof.
  refine
    {|
      encode_code := CAtom;
      decode_code :=
        fun c =>
          match c with
          | CAtom n => Some n
          | _ => None
          end
    |}.
  intros n; reflexivity.
Defined.

Definition encode_nat_list (xs : list nat) : code :=
  encode_code_list CAtom xs.

Definition decode_nat_list (c : code) : option (list nat) :=
  decode_code_list_node
    (fun c =>
       match c with
       | CAtom n => Some n
       | _ => None
       end) c.

Lemma decode_nat_list_encode :
  forall xs, decode_nat_list (encode_nat_list xs) = Some xs.
Proof.
  intros xs.
  apply decode_code_list_node_encode.
  intros n; reflexivity.
Qed.

Fixpoint encode_prcode (p : K.PRCode) : code :=
  match p with
  | K.PRConst n => CNode 10 [CAtom n]
  | K.PRArg n => CNode 11 [CAtom n]
  | K.PRSucc a => CNode 12 [encode_prcode a]
  | K.PRPred a => CNode 13 [encode_prcode a]
  | K.PRAdd a b => CNode 14 [encode_prcode a; encode_prcode b]
  | K.PRMul a b => CNode 15 [encode_prcode a; encode_prcode b]
  | K.PREq a b => CNode 16 [encode_prcode a; encode_prcode b]
  | K.PRLe a b => CNode 17 [encode_prcode a; encode_prcode b]
  | K.PRNot a => CNode 18 [encode_prcode a]
  | K.PRAnd a b => CNode 19 [encode_prcode a; encode_prcode b]
  | K.PROr a b => CNode 20 [encode_prcode a; encode_prcode b]
  | K.PRIf g t e => CNode 21 [encode_prcode g; encode_prcode t; encode_prcode e]
  end.

Fixpoint decode_prcode (c : code) : option K.PRCode :=
  match c with
  | CNode 10 [CAtom n] => Some (K.PRConst n)
  | CNode 11 [CAtom n] => Some (K.PRArg n)
  | CNode 12 [a] =>
      match decode_prcode a with
      | Some a' => Some (K.PRSucc a')
      | None => None
      end
  | CNode 13 [a] =>
      match decode_prcode a with
      | Some a' => Some (K.PRPred a')
      | None => None
      end
  | CNode 14 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PRAdd a' b')
      | _, _ => None
      end
  | CNode 15 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PRMul a' b')
      | _, _ => None
      end
  | CNode 16 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PREq a' b')
      | _, _ => None
      end
  | CNode 17 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PRLe a' b')
      | _, _ => None
      end
  | CNode 18 [a] =>
      match decode_prcode a with
      | Some a' => Some (K.PRNot a')
      | None => None
      end
  | CNode 19 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PRAnd a' b')
      | _, _ => None
      end
  | CNode 20 [a; b] =>
      match decode_prcode a, decode_prcode b with
      | Some a', Some b' => Some (K.PROr a' b')
      | _, _ => None
      end
  | CNode 21 [g; t; e] =>
      match decode_prcode g, decode_prcode t, decode_prcode e with
      | Some g', Some t', Some e' => Some (K.PRIf g' t' e')
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma decode_encode_prcode :
  forall p, decode_prcode (encode_prcode p) = Some p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
    try rewrite IHp3; reflexivity.
Qed.

Definition prcode_structural_codec : StructuralCodec K.PRCode.
Proof.
  refine {| encode_code := encode_prcode; decode_code := decode_prcode |}.
  exact decode_encode_prcode.
Defined.

Fixpoint encode_term (t : B.term) : code :=
  match t with
  | S2.RVar n => CNode 30 [CAtom n]
  | S2.RConst n => CNode 31 [CAtom n]
  | S2.RApp l r => CNode 32 [encode_term l; encode_term r]
  | S2.RBind body => CNode 33 [encode_term body]
  end.

Fixpoint decode_term (c : code) : option B.term :=
  match c with
  | CNode 30 [CAtom n] => Some (B.mk_var n)
  | CNode 31 [CAtom n] => Some (B.mk_const n)
  | CNode 32 [l; r] =>
      match decode_term l, decode_term r with
      | Some l', Some r' => Some (B.mk_app l' r')
      | _, _ => None
      end
  | CNode 33 [body] =>
      match decode_term body with
      | Some body' => Some (B.mk_bind body')
      | None => None
      end
  | _ => None
  end.

Lemma decode_encode_term :
  forall t, decode_term (encode_term t) = Some t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Definition term_structural_codec : StructuralCodec B.term.
Proof.
  refine {| encode_code := encode_term; decode_code := decode_term |}.
  exact decode_encode_term.
Defined.

Definition encode_context (ctx : R.context) : code :=
  encode_code_list encode_term ctx.

Definition decode_context (c : code) : option R.context :=
  decode_code_list_node decode_term c.

Lemma decode_encode_context :
  forall ctx, decode_context (encode_context ctx) = Some ctx.
Proof.
  intros ctx.
  apply decode_code_list_node_encode.
  exact decode_encode_term.
Qed.

Definition context_structural_codec : StructuralCodec R.context.
Proof.
  refine {| encode_code := encode_context; decode_code := decode_context |}.
  exact decode_encode_context.
Defined.

Definition encode_judgment (j : R.judgment) : code :=
  match j with
  | R.JFormula t => CNode 40 [encode_term t]
  | R.JSequent ctx t => CNode 41 [encode_context ctx; encode_term t]
  end.

Definition decode_judgment (c : code) : option R.judgment :=
  match c with
  | CNode 40 [t] =>
      match decode_term t with
      | Some t' => Some (R.JFormula t')
      | None => None
      end
  | CNode 41 [ctx; t] =>
      match decode_context ctx, decode_term t with
      | Some ctx', Some t' => Some (R.JSequent ctx' t')
      | _, _ => None
      end
  | _ => None
  end.

Lemma decode_encode_judgment :
  forall j, decode_judgment (encode_judgment j) = Some j.
Proof.
  intros [t | ctx t].
  - simpl; rewrite decode_encode_term; reflexivity.
  - unfold encode_judgment, decode_judgment.
    rewrite decode_encode_context, decode_encode_term.
    reflexivity.
Qed.

Definition judgment_structural_codec : StructuralCodec R.judgment.
Proof.
  refine {| encode_code := encode_judgment; decode_code := decode_judgment |}.
  exact decode_encode_judgment.
Defined.

Fixpoint encode_proof_object (p : R.proof_object) : code :=
  match p with
  | R.PAxiom j => CNode 50 [encode_judgment j]
  | R.PRule idx ps => CNode 51 [CAtom idx; encode_code_list encode_proof_object ps]
  end.

Fixpoint decode_proof_object (c : code) : option R.proof_object :=
  match c with
  | CNode 50 [j] =>
      match decode_judgment j with
      | Some j' => Some (R.PAxiom j')
      | None => None
      end
  | CNode 51 [CAtom idx; ps] =>
      match decode_code_list_node decode_proof_object ps with
      | Some ps' => Some (R.PRule idx ps')
      | None => None
      end
  | _ => None
  end.

Lemma decode_encode_proof_object :
  forall p, decode_proof_object (encode_proof_object p) = Some p.
Proof.
  fix IH 1.
  intros p.
  destruct p as [j | idx ps]; simpl.
  - rewrite decode_encode_judgment; reflexivity.
  - assert
      (Hlist :
        forall qs,
          decode_code_list decode_proof_object
            (map encode_proof_object qs) = Some qs).
    {
      induction qs as [|q qs IHqs]; simpl.
      - reflexivity.
      - rewrite IH, IHqs; reflexivity.
    }
    unfold decode_code_list_node, encode_code_list.
    rewrite Hlist.
    reflexivity.
Qed.

Definition proof_object_structural_codec : StructuralCodec R.proof_object.
Proof.
  refine {| encode_code := encode_proof_object; decode_code := decode_proof_object |}.
  exact decode_encode_proof_object.
Defined.

Definition decoded_check_proof
           (spec : R.TheorySpec) (proof_code goal_code : code) : bool :=
  match decode_proof_object proof_code, decode_judgment goal_code with
  | Some p, Some goal => R.check_proof spec p goal
  | _, _ => false
  end.

Lemma decoded_check_proof_agrees :
  forall spec p goal,
    decoded_check_proof spec (encode_proof_object p) (encode_judgment goal) =
    R.check_proof spec p goal.
Proof.
  intros spec p goal.
  unfold decoded_check_proof.
  rewrite decode_encode_proof_object, decode_encode_judgment.
  reflexivity.
Qed.

Lemma decoded_example_rule_checked :
  decoded_check_proof R.example_rule_theory
                      (encode_proof_object R.example_rule_proof)
                      (encode_judgment (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite decoded_check_proof_agrees.
  exact R.example_rule_checked.
Qed.

End FormalSystemFactoryStructuralCodec.

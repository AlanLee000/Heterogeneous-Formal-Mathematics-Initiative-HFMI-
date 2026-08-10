From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import ListNotations.


Module OwnershipTransferBindingLogic.

Definition Name := nat.
Definition Obj := nat.
Definition Own := nat.

Inductive Mode : Type :=
| MRead
| MWrite.

Inductive KTagName : Type :=
| KTagNone
| KTagRead
| KTagMove
| KTagCopy
| KTagDrop
| KTagSubst.

Inductive DTagName : Type :=
| DTagInit.

Section GenericSignature.

Variable G : Type.
Variable R : Type.
Variable arG : G -> nat.
Variable arR : R -> nat.

Inductive SymCode : Type :=
| GCode : G -> SymCode
| RCode : R -> SymCode.

Inductive Tag : Type :=
| TagVCore
| TagOCore
| TagPCore
| TagCCore
| TagGCore
| TagDCore
| TagQCore
| TagShEq
| TagShRel
| TagShLe
| TagShOwn
| TagShPort
| TagShNeg
| TagShImp
| TagShAll
| TagShBeh
| TagShNone
| TagShRead
| TagShMove
| TagShCopy
| TagShDrop
| TagShSubst.

Inductive Core : Type :=
| CNat : nat -> Core
| CName : Name -> Core
| CObj : Obj -> Core
| COwn : Own -> Core
| CMode : Mode -> Core
| CKTag : KTagName -> Core
| CDTag : DTagName -> Core
| CTag : Tag -> Core
| CSym : SymCode -> Core
| CSeq : list Core -> Core.

Definition gcode (g : G) : SymCode := GCode g.
Definition rcode (r : R) : SymCode := RCode r.

Definition tagged (tag : Tag) (xs : list Core) : Core :=
  CSeq (CTag tag :: xs).

Definition vcore (xi : Obj) : Core := tagged TagVCore [CObj xi].
Definition ocore (o : Own) : Core := tagged TagOCore [COwn o].
Definition pcore (r : nat) (a b : Core) : Core :=
  tagged TagPCore [CNat r; a; b].
Definition ccore (p q : Core) : Core := tagged TagCCore [p; q].
Definition gcore (g : G) (args : list Core) : Core :=
  tagged TagGCore [CSym (gcode g); CNat (arG g); CSeq args].
Definition dcore (d u : Core) : Core := tagged TagDCore [d; u].
Definition qcore (c : Core) : Core := tagged TagQCore [c].

Definition sh_eq (s t : Core) : Core := tagged TagShEq [s; t].
Definition sh_rel (rel : R) (args : list Core) : Core :=
  tagged TagShRel [CSym (rcode rel); CNat (arR rel); CSeq args].
Definition sh_le (s t : Core) : Core := tagged TagShLe [s; t].
Definition sh_own (m : Mode) (o t : Core) : Core :=
  tagged TagShOwn [CMode m; o; t].
Definition sh_port (delta : Core) : Core := tagged TagShPort [delta].
Definition sh_neg (a : Core) : Core := tagged TagShNeg [a].
Definition sh_imp (a b : Core) : Core := tagged TagShImp [a; b].
Definition sh_all (d o b c a : Core) : Core :=
  tagged TagShAll [d; o; b; c; a].
Definition sh_beh (c d delta : Core) : Core :=
  tagged TagShBeh [c; d; delta].
Definition sh_none : Core := tagged TagShNone [].
Definition sh_read (a delta : Core) : Core := tagged TagShRead [a; delta].
Definition sh_move (a b delta : Core) : Core :=
  tagged TagShMove [a; b; delta].
Definition sh_copy (a b delta : Core) : Core :=
  tagged TagShCopy [a; b; delta].
Definition sh_drop (a delta : Core) : Core := tagged TagShDrop [a; delta].
Definition sh_subst (a delta s : Core) : Core :=
  tagged TagShSubst [a; delta; s].

Fixpoint fresh_from (fuel n : nat) (xs : list nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
      if in_dec Nat.eq_dec n xs
      then fresh_from fuel' (S n) xs
      else n
  end.

Definition freshName (xs : list Name) : Name :=
  fresh_from (S (length xs)) 0 xs.

Definition freshObj (xs : list Obj) : Obj :=
  fresh_from (S (length xs)) 0 xs.

Inductive Dep : Type :=
| DepInit
| DepPair : nat -> nat -> Dep.

Inductive Term : Type :=
| TVar : Name -> Obj -> Term
| TOwner : Own -> Term
| TPath : nat -> Term -> Term -> Term
| TComp : Term -> Term -> Term
| TOp : G -> Terms -> Term
| TDecl : Term -> Term -> Term
| TQuote : Ctx -> Term
with Terms : Type :=
| TNil : Terms
| TCons : Term -> Terms -> Terms
with Frm : Type :=
| FEq : Term -> Term -> Frm
| FRel : R -> Terms -> Frm
| FLe : Term -> Term -> Frm
| FOwn : Mode -> Term -> Term -> Frm
| FPort : Core -> Frm
| FNeg : Frm -> Frm
| FImp : Frm -> Frm -> Frm
| FAll : Term -> Term -> Term -> Ctx -> Frm -> Frm
| FBeh : Ctx -> Ctx -> Core -> Frm
with KAct : Type :=
| KNone : KAct
| KRead : Term -> Core -> KAct
| KMove : Term -> Term -> Core -> KAct
| KCopy : Term -> Term -> Core -> KAct
| KDrop : Term -> Core -> KAct
| KSubst : Term -> Core -> Term -> KAct
with Cert : Type :=
| CertLine : Term -> Frm -> Dep -> Dep -> KAct -> Cert
with Ctx : Type :=
| CtxNil : Ctx
| CtxCons : Cert -> Ctx -> Ctx.

Fixpoint term_core (t : Term) {struct t} : Core :=
  match t with
  | TVar _ xi => vcore xi
  | TOwner o => ocore o
  | TPath r a b => pcore r (term_core a) (term_core b)
  | TComp p q => ccore (term_core p) (term_core q)
  | TOp g ts => gcore g (terms_core ts)
  | TDecl d u => dcore (term_core d) (term_core u)
  | TQuote c => qcore (ctx_shape c)
  end
with terms_core (ts : Terms) {struct ts} : list Core :=
  match ts with
  | TNil => []
  | TCons t ts' => term_core t :: terms_core ts'
  end
with fshape (a : Frm) {struct a} : Core :=
  match a with
  | FEq s t => sh_eq (term_core s) (term_core t)
  | FRel rel ts => sh_rel rel (terms_core ts)
  | FLe s t => sh_le (term_core s) (term_core t)
  | FOwn m o t => sh_own m (term_core o) (term_core t)
  | FPort delta => sh_port delta
  | FNeg b => sh_neg (fshape b)
  | FImp b c => sh_imp (fshape b) (fshape c)
  | FAll d o b c body =>
      sh_all (term_core d) (term_core o) (term_core b) (ctx_shape c)
        (fshape body)
  | FBeh c d delta => sh_beh (ctx_shape c) (ctx_shape d) delta
  end
with kshape (k : KAct) {struct k} : Core :=
  match k with
  | KNone => sh_none
  | KRead a delta => sh_read (term_core a) delta
  | KMove a b delta => sh_move (term_core a) (term_core b) delta
  | KCopy a b delta => sh_copy (term_core a) (term_core b) delta
  | KDrop a delta => sh_drop (term_core a) delta
  | KSubst a delta s => sh_subst (term_core a) delta (term_core s)
  end
with cert_shape (c : Cert) {struct c} : Core :=
  match c with
  | CertLine p a mu tau k =>
      let dep_shape (d : Dep) : Core :=
        match d with
        | DepInit => CDTag DTagInit
        | DepPair i j => CSeq [CNat i; CNat j]
        end in
      CSeq [term_core p; fshape a; dep_shape mu; dep_shape tau; kshape k]
  end
with ctx_shape (c : Ctx) {struct c} : Core :=
  match c with
  | CtxNil => CSeq []
  | CtxCons line rest =>
      match ctx_shape rest with
      | CSeq xs => CSeq (cert_shape line :: xs)
      | x => CSeq [cert_shape line; x]
      end
  end.

Definition Path := list nat.

Fixpoint terms_nth (ts : Terms) (i : nat) : option Term :=
  match ts, i with
  | TNil, _ => None
  | TCons t _, O => Some t
  | TCons _ rest, S i' => terms_nth rest i'
  end.

Fixpoint terms_length (ts : Terms) : nat :=
  match ts with
  | TNil => 0
  | TCons _ rest => S (terms_length rest)
  end.

Fixpoint subterm_at (t : Term) (p : Path) : option Term :=
  match p with
  | [] => Some t
  | i :: p' =>
      match t with
      | TPath _ a b | TComp a b | TDecl a b =>
          match i with
          | O => subterm_at a p'
          | S O => subterm_at b p'
          | _ => None
          end
      | TOp _ ts =>
          match terms_nth ts i with
          | Some u => subterm_at u p'
          | None => None
          end
      | _ => None
      end
  end.

Definition Pos (t : Term) (p : Path) : Prop :=
  exists u, subterm_at t p = Some u.

Definition Prefix (p q : Path) : Prop := exists r, q = p ++ r.
Definition ProperPrefix (p q : Path) : Prop := Prefix p q /\ p <> q.

Definition SetOf (A : Type) := A -> Prop.

Fixpoint InTerms (t : Term) (ts : Terms) : Prop :=
  match ts with
  | TNil => False
  | TCons u rest => t = u \/ InTerms t rest
  end.

Fixpoint DecT (t : Term) (p : Path) {struct t} : Prop :=
  match t with
  | TVar _ _ => False
  | TOwner _ => False
  | TQuote _ => False
  | TPath _ a b | TComp a b =>
      (exists q, p = 0 :: q /\ DecT a q) \/
      (exists q, p = 1 :: q /\ DecT b q)
  | TOp _ ts =>
      exists i q, p = i :: q /\ DecTerms ts i q
  | TDecl d u =>
      (exists q, p = 0 :: q /\ Pos d q) \/
      (exists q, p = 1 :: q /\ DecT u q)
  end
with DecTerms (ts : Terms) (i : nat) (p : Path) {struct ts} : Prop :=
  match ts with
  | TNil => False
  | TCons t rest =>
      (i = 0 /\ DecT t p) \/
      exists j, i = S j /\ DecTerms rest j p
  end.

Fixpoint FrT (t : Term) (p : Path) {struct t} : Prop :=
  match t with
  | TVar _ _ => p = []
  | TOwner _ => p = []
  | TQuote _ => p = []
  | TPath _ a b | TComp a b =>
      p = [] \/
      (exists q, p = 0 :: q /\ FrT a q) \/
      (exists q, p = 1 :: q /\ FrT b q)
  | TOp _ ts =>
      p = [] \/
      exists i q, p = i :: q /\ FrTerms ts i q
  | TDecl d u =>
      p = [] \/
      (exists q,
        p = 1 :: q /\
        FrT u q /\
        ~ (exists q0 p0 uq,
            q = q0 ++ p0 /\
            FrT u q0 /\
            (exists root, subterm_at u q0 = Some root /\
              term_core root = term_core d) /\
            (forall q' uq',
              FrT u q' ->
              ProperPrefix q' q0 ->
              subterm_at u q' = Some uq' ->
              term_core uq' <> term_core d) /\
            subterm_at u q0 = Some uq /\
            Pos uq p0 /\
            ~ DecT u (q0 ++ p0)))
  end
with FrTerms (ts : Terms) (i : nat) (p : Path) {struct ts} : Prop :=
  match ts with
  | TNil => False
  | TCons t rest =>
      (i = 0 /\ FrT t p) \/
      exists j, i = S j /\ FrTerms rest j p
  end.

Fixpoint BdT (t : Term) (p : Path) {struct t} : Prop :=
  match t with
  | TVar _ _ => False
  | TOwner _ => False
  | TQuote _ => False
  | TPath _ a b | TComp a b =>
      (exists q, p = 0 :: q /\ BdT a q) \/
      (exists q, p = 1 :: q /\ BdT b q)
  | TOp _ ts =>
      exists i q, p = i :: q /\ BdTerms ts i q
  | TDecl d u =>
      exists q,
        p = 1 :: q /\
        (BdT u q \/
          exists q0 p0 uq,
            q = q0 ++ p0 /\
            FrT u q0 /\
            (exists root, subterm_at u q0 = Some root /\
              term_core root = term_core d) /\
            (forall q' uq',
              FrT u q' ->
              ProperPrefix q' q0 ->
              subterm_at u q' = Some uq' ->
              term_core uq' <> term_core d) /\
            subterm_at u q0 = Some uq /\
            Pos uq p0 /\
            ~ DecT u (q0 ++ p0))
  end
with BdTerms (ts : Terms) (i : nat) (p : Path) {struct ts} : Prop :=
  match ts with
  | TNil => False
  | TCons t rest =>
      (i = 0 /\ BdT t p) \/
      exists j, i = S j /\ BdTerms rest j p
  end.

Definition OpenRoot (d u : Term) (q : Path) : Prop :=
  FrT u q /\
  (exists uq, subterm_at u q = Some uq /\ term_core uq = term_core d) /\
  forall q' uq',
    FrT u q' ->
    ProperPrefix q' q ->
    subterm_at u q' = Some uq' ->
    term_core uq' <> term_core d.

Definition Cap (d u : Term) (r : Path) : Prop :=
  exists q p uq,
    r = q ++ p /\
    OpenRoot d u q /\
    subterm_at u q = Some uq /\
    Pos uq p /\
    ~ DecT u (q ++ p).

Definition FCoreT (t : Term) (delta : Core) : Prop :=
  exists p u, FrT t p /\ subterm_at t p = Some u /\ delta = term_core u.

Definition BCoreT (t : Term) (delta : Core) : Prop :=
  exists p u, BdT t p /\ subterm_at t p = Some u /\ delta = term_core u.

Fixpoint FCoreTerms (ts : Terms) (delta : Core) : Prop :=
  match ts with
  | TNil => False
  | TCons t rest => FCoreT t delta \/ FCoreTerms rest delta
  end.

Definition FCoreK (k : KAct) (delta : Core) : Prop :=
  match k with
  | KNone => False
  | KRead a epsilon => FCoreT a delta \/ delta = epsilon
  | KMove a b epsilon | KCopy a b epsilon =>
      FCoreT a delta \/ FCoreT b delta \/ delta = epsilon
  | KDrop a epsilon => FCoreT a delta \/ delta = epsilon
  | KSubst a epsilon s => FCoreT a delta \/ FCoreT s delta \/ delta = epsilon
  end.

Fixpoint FCoreF (a : Frm) (delta : Core) : Prop :=
  match a with
  | FEq s t => FCoreT s delta \/ FCoreT t delta
  | FRel _ ts => FCoreTerms ts delta
  | FLe s t => FCoreT s delta \/ FCoreT t delta
  | FOwn _ o t => FCoreT o delta \/ FCoreT t delta
  | FPort epsilon => delta = epsilon
  | FNeg b => FCoreF b delta
  | FImp b c => FCoreF b delta \/ FCoreF c delta
  | FAll d o b c body =>
      FCoreT d delta \/
      FCoreT o delta \/
      FCoreT b delta \/
      FCoreC c delta \/
      (FCoreF body delta /\ delta <> term_core d)
  | FBeh c d epsilon => FCoreC c delta \/ FCoreC d delta \/ delta = epsilon
  end
with FCoreC (c : Ctx) (delta : Core) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine p a _ _ k) rest =>
      FCoreT p delta \/ FCoreF a delta \/ FCoreK k delta \/ FCoreC rest delta
  end.

Fixpoint BCoreTerms (ts : Terms) (delta : Core) : Prop :=
  match ts with
  | TNil => False
  | TCons t rest => BCoreT t delta \/ BCoreTerms rest delta
  end.

Definition BCoreK (k : KAct) (delta : Core) : Prop :=
  match k with
  | KNone => False
  | KRead a _ => BCoreT a delta
  | KMove a b _ | KCopy a b _ => BCoreT a delta \/ BCoreT b delta
  | KDrop a _ => BCoreT a delta
  | KSubst a _ s => BCoreT a delta \/ BCoreT s delta
  end.

Fixpoint BCoreF (a : Frm) (delta : Core) : Prop :=
  match a with
  | FEq s t => BCoreT s delta \/ BCoreT t delta
  | FRel _ ts => BCoreTerms ts delta
  | FLe s t => BCoreT s delta \/ BCoreT t delta
  | FOwn _ o t => BCoreT o delta \/ BCoreT t delta
  | FPort _ => False
  | FNeg b => BCoreF b delta
  | FImp b c => BCoreF b delta \/ BCoreF c delta
  | FAll d o b c body =>
      BCoreT d delta \/
      BCoreT o delta \/
      BCoreT b delta \/
      BCoreC c delta \/
      BCoreF body delta \/
      delta = term_core d
  | FBeh c d _ => BCoreC c delta \/ BCoreC d delta
  end
with BCoreC (c : Ctx) (delta : Core) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine p a _ _ k) rest =>
      BCoreT p delta \/ BCoreF a delta \/ BCoreK k delta \/ BCoreC rest delta
  end.

Definition FRoot (delta : Core) (t : Term) (p : Path) : Prop :=
  FrT t p /\
  (exists u, subterm_at t p = Some u /\ term_core u = delta) /\
  forall q u,
    FrT t q ->
    ProperPrefix q p ->
    subterm_at t q = Some u ->
    term_core u <> delta.

Definition ActCore (t : Term) (p : Path) (delta : Core) : Prop :=
  exists r d u v,
    subterm_at t r = Some (TDecl d u) /\
    p = r ++ [1] ++ v /\
    delta = term_core d.

Definition CAOKT (t : Term) (delta : Core) (s : Term) : Prop :=
  forall p gamma,
    FRoot delta t p ->
    FCoreT s gamma ->
    ~ ActCore t p gamma.

Definition NameObjT (t : Term) (x : Name) (xi : Obj) : Prop :=
  exists p, FrT t p /\ subterm_at t p = Some (TVar x xi).

Fixpoint NameObjTerms (ts : Terms) (x : Name) (xi : Obj) : Prop :=
  match ts with
  | TNil => False
  | TCons t rest => NameObjT t x xi \/ NameObjTerms rest x xi
  end.

Definition NameObjK (k : KAct) (x : Name) (xi : Obj) : Prop :=
  match k with
  | KNone => False
  | KRead a _ => NameObjT a x xi
  | KMove a b _ | KCopy a b _ => NameObjT a x xi \/ NameObjT b x xi
  | KDrop a _ => NameObjT a x xi
  | KSubst a _ s => NameObjT a x xi \/ NameObjT s x xi
  end.

Fixpoint NameObjF (a : Frm) (x : Name) (xi : Obj) : Prop :=
  match a with
  | FEq s t => NameObjT s x xi \/ NameObjT t x xi
  | FRel _ ts => NameObjTerms ts x xi
  | FLe s t => NameObjT s x xi \/ NameObjT t x xi
  | FOwn _ o t => NameObjT o x xi \/ NameObjT t x xi
  | FPort _ => False
  | FNeg b => NameObjF b x xi
  | FImp b c => NameObjF b x xi \/ NameObjF c x xi
  | FAll d o b c body =>
      NameObjT d x xi \/
      NameObjT o x xi \/
      NameObjT b x xi \/
      NameObjC c x xi \/
      (NameObjF body x xi /\ vcore xi <> term_core d)
  | FBeh c d _ => NameObjC c x xi \/ NameObjC d x xi
  end
with NameObjC (c : Ctx) (x : Name) (xi : Obj) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine p a _ _ k) rest =>
      NameObjT p x xi \/ NameObjF a x xi \/ NameObjK k x xi \/ NameObjC rest x xi
  end.

Definition NameOK (a : Frm) : Prop :=
  forall x xi eta,
    NameObjF a x xi ->
    NameObjF a x eta ->
    xi = eta.

Inductive WellTerm : Term -> Prop :=
| WellTVar :
    forall x xi, WellTerm (TVar x xi)
| WellTOwner :
    forall o, WellTerm (TOwner o)
| WellTPath :
    forall r a b,
      WellTerm a ->
      WellTerm b ->
      WellTerm (TPath r a b)
| WellTComp :
    forall a b,
      WellTerm a ->
      WellTerm b ->
      WellTerm (TComp a b)
| WellTOp :
    forall g ts,
      WellTerms ts ->
      terms_length ts = arG g ->
      WellTerm (TOp g ts)
| WellTDecl :
    forall d u,
      WellTerm d ->
      WellTerm u ->
      WellTerm (TDecl d u)
| WellTQuote :
    forall c,
      WellCtxStruct c ->
      WellTerm (TQuote c)
with WellTerms : Terms -> Prop :=
| WellTNil :
    WellTerms TNil
| WellTCons :
    forall t rest,
      WellTerm t ->
      WellTerms rest ->
      WellTerms (TCons t rest)
with WellFrm : Frm -> Prop :=
| WellFEq :
    forall s t,
      WellTerm s ->
      WellTerm t ->
      WellFrm (FEq s t)
| WellFRel :
    forall rel ts,
      WellTerms ts ->
      terms_length ts = arR rel ->
      WellFrm (FRel rel ts)
| WellFLe :
    forall s t,
      WellTerm s ->
      WellTerm t ->
      WellFrm (FLe s t)
| WellFOwn :
    forall m o t,
      WellTerm o ->
      WellTerm t ->
      WellFrm (FOwn m o t)
| WellFPort :
    forall delta, WellFrm (FPort delta)
| WellFNeg :
    forall a,
      WellFrm a ->
      WellFrm (FNeg a)
| WellFImp :
    forall a b,
      WellFrm a ->
      WellFrm b ->
      WellFrm (FImp a b)
| WellFAll :
    forall d o b c a,
      WellTerm d ->
      WellTerm o ->
      WellTerm b ->
      WellCtxStruct c ->
      WellFrm a ->
      WellFrm (FAll d o b c a)
| WellFBeh :
    forall c d delta,
      WellCtxStruct c ->
      WellCtxStruct d ->
      WellFrm (FBeh c d delta)
with WellKAct : KAct -> Prop :=
| WellKNone :
    WellKAct KNone
| WellKRead :
    forall a delta,
      WellTerm a ->
      WellKAct (KRead a delta)
| WellKMove :
    forall a b delta,
      WellTerm a ->
      WellTerm b ->
      WellKAct (KMove a b delta)
| WellKCopy :
    forall a b delta,
      WellTerm a ->
      WellTerm b ->
      WellKAct (KCopy a b delta)
| WellKDrop :
    forall a delta,
      WellTerm a ->
      WellKAct (KDrop a delta)
| WellKSubst :
    forall a delta s,
      WellTerm a ->
      WellTerm s ->
      WellKAct (KSubst a delta s)
with WellCert : Cert -> Prop :=
| WellCertLine :
    forall p a mu tau k,
      WellTerm p ->
      WellFrm a ->
      WellKAct k ->
      WellCert (CertLine p a mu tau k)
with WellCtxStruct : Ctx -> Prop :=
| WellCtxNil :
    WellCtxStruct CtxNil
| WellCtxCons :
    forall line rest,
      WellCert line ->
      WellCtxStruct rest ->
      WellCtxStruct (CtxCons line rest).

Fixpoint cert_at (c : Ctx) (i : nat) : option Cert :=
  match c, i with
  | CtxNil, _ => None
  | CtxCons line _, O => Some line
  | CtxCons _ rest, S i' => cert_at rest i'
  end.

Definition cert_path (line : Cert) : Term :=
  match line with CertLine p _ _ _ _ => p end.

Definition cert_formula (line : Cert) : Frm :=
  match line with CertLine _ a _ _ _ => a end.

Inductive EndMinus : Term -> Term -> Prop :=
| EndMinusPath :
    forall r a b, EndMinus (TPath r a b) a
| EndMinusComp :
    forall p q a m,
      EndMinus p a ->
      EndPlus p m ->
      EndMinus q m ->
      EndMinus (TComp p q) a
with EndPlus : Term -> Term -> Prop :=
| EndPlusPath :
    forall r a b, EndPlus (TPath r a b) b
| EndPlusComp :
    forall p q b m,
      EndPlus q b ->
      EndPlus p m ->
      EndMinus q m ->
      EndPlus (TComp p q) b.

Definition DepOKFormula (c : Ctx) (i : nat) (ai : Frm) (mu : Dep) : Prop :=
  match mu with
  | DepInit => True
  | DepPair j k =>
      j < i /\
      k < i /\
      exists linej linek,
        cert_at c j = Some linej /\
        cert_at c k = Some linek /\
        cert_formula linek = FImp (cert_formula linej) ai
  end.

Definition DepOKTerm (c : Ctx) (i : nat) (pi : Term) (tau : Dep) : Prop :=
  match tau with
  | DepInit => True
  | DepPair r s =>
      r < i /\
      s < i /\
      exists liner lines mid,
        cert_at c r = Some liner /\
        cert_at c s = Some lines /\
        EndPlus (cert_path liner) mid /\
        EndMinus (cert_path lines) mid /\
        pi = TComp (cert_path liner) (cert_path lines)
  end.

Definition CertOKAt (c : Ctx) (i : nat) (line : Cert) : Prop :=
  match line with
  | CertLine p a mu tau _ =>
      WellCert line /\ DepOKFormula c i a mu /\ DepOKTerm c i p tau
  end.

Definition CtxOK (c : Ctx) : Prop :=
  WellCtxStruct c /\ forall i line, cert_at c i = Some line -> CertOKAt c i line.

Inductive SubCoreT : Term -> Core -> Term -> Term -> Prop :=
| SCTRoot :
    forall t delta s,
      CAOKT t delta s ->
      FRoot delta t [] ->
      SubCoreT t delta s s
| SCTVar :
    forall x xi delta s,
      CAOKT (TVar x xi) delta s ->
      ~ FRoot delta (TVar x xi) [] ->
      SubCoreT (TVar x xi) delta s (TVar x xi)
| SCTOwner :
    forall o delta s,
      CAOKT (TOwner o) delta s ->
      ~ FRoot delta (TOwner o) [] ->
      SubCoreT (TOwner o) delta s (TOwner o)
| SCTPath :
    forall r a b delta s a' b',
      CAOKT (TPath r a b) delta s ->
      ~ FRoot delta (TPath r a b) [] ->
      SubCoreT a delta s a' ->
      SubCoreT b delta s b' ->
      SubCoreT (TPath r a b) delta s (TPath r a' b')
| SCTComp :
    forall a b delta s a' b',
      CAOKT (TComp a b) delta s ->
      ~ FRoot delta (TComp a b) [] ->
      SubCoreT a delta s a' ->
      SubCoreT b delta s b' ->
      SubCoreT (TComp a b) delta s (TComp a' b')
| SCTOp :
    forall g ts delta s ts',
      CAOKT (TOp g ts) delta s ->
      ~ FRoot delta (TOp g ts) [] ->
      SubCoreTerms ts delta s ts' ->
      SubCoreT (TOp g ts) delta s (TOp g ts')
| SCTDecl :
    forall d u delta s d' u',
      CAOKT (TDecl d u) delta s ->
      ~ FRoot delta (TDecl d u) [] ->
      SubCoreT d delta s d' ->
      SubCoreT u delta s u' ->
      SubCoreT (TDecl d u) delta s (TDecl d' u')
| SCTQuote :
    forall c delta s c',
      CAOKT (TQuote c) delta s ->
      ~ FRoot delta (TQuote c) [] ->
      SubCoreC c delta s c' ->
      SubCoreT (TQuote c) delta s (TQuote c')
with SubCoreTerms : Terms -> Core -> Term -> Terms -> Prop :=
| SCTermsNil :
    forall delta s, SubCoreTerms TNil delta s TNil
| SCTermsCons :
    forall t rest delta s t' rest',
      SubCoreT t delta s t' ->
      SubCoreTerms rest delta s rest' ->
      SubCoreTerms (TCons t rest) delta s (TCons t' rest')
with SubCoreF : Frm -> Core -> Term -> Frm -> Prop :=
| SCFEq :
    forall u v delta s u' v',
      SubCoreT u delta s u' ->
      SubCoreT v delta s v' ->
      SubCoreF (FEq u v) delta s (FEq u' v')
| SCFRel :
    forall rel ts delta s ts',
      SubCoreTerms ts delta s ts' ->
      SubCoreF (FRel rel ts) delta s (FRel rel ts')
| SCFLe :
    forall u v delta s u' v',
      SubCoreT u delta s u' ->
      SubCoreT v delta s v' ->
      SubCoreF (FLe u v) delta s (FLe u' v')
| SCFOwn :
    forall m o t delta s o' t',
      SubCoreT o delta s o' ->
      SubCoreT t delta s t' ->
      SubCoreF (FOwn m o t) delta s (FOwn m o' t')
| SCFPort :
    forall epsilon delta s,
      SubCoreF (FPort epsilon) delta s (FPort epsilon)
| SCFNeg :
    forall a delta s a',
      SubCoreF a delta s a' ->
      SubCoreF (FNeg a) delta s (FNeg a')
| SCFImp :
    forall a b delta s a' b',
      SubCoreF a delta s a' ->
      SubCoreF b delta s b' ->
      SubCoreF (FImp a b) delta s (FImp a' b')
| SCFAllShadow :
    forall d o b c a delta s,
      term_core d = delta ->
      SubCoreF (FAll d o b c a) delta s (FAll d o b c a)
| SCFAll :
    forall d o b c a delta s d' o' b' c' a',
      term_core d <> delta ->
      SubCoreT d delta s d' ->
      SubCoreT o delta s o' ->
      SubCoreT b delta s b' ->
      SubCoreC c delta s c' ->
      SubCoreF a delta s a' ->
      SubCoreF (FAll d o b c a) delta s (FAll d' o' b' c' a')
| SCFBeh :
    forall c d epsilon delta s c' d',
      SubCoreC c delta s c' ->
      SubCoreC d delta s d' ->
      SubCoreF (FBeh c d epsilon) delta s (FBeh c' d' epsilon)
with SubCoreK : KAct -> Core -> Term -> KAct -> Prop :=
| SCKNone :
    forall delta s, SubCoreK KNone delta s KNone
| SCKRead :
    forall a epsilon delta s a',
      SubCoreT a delta s a' ->
      SubCoreK (KRead a epsilon) delta s (KRead a' epsilon)
| SCKMove :
    forall a b epsilon delta s a' b',
      SubCoreT a delta s a' ->
      SubCoreT b delta s b' ->
      SubCoreK (KMove a b epsilon) delta s (KMove a' b' epsilon)
| SCKCopy :
    forall a b epsilon delta s a' b',
      SubCoreT a delta s a' ->
      SubCoreT b delta s b' ->
      SubCoreK (KCopy a b epsilon) delta s (KCopy a' b' epsilon)
| SCKDrop :
    forall a epsilon delta s a',
      SubCoreT a delta s a' ->
      SubCoreK (KDrop a epsilon) delta s (KDrop a' epsilon)
| SCKSubst :
    forall a epsilon u delta s a' u',
      SubCoreT a delta s a' ->
      SubCoreT u delta s u' ->
      SubCoreK (KSubst a epsilon u) delta s (KSubst a' epsilon u')
with SubCoreCert : Cert -> Core -> Term -> Cert -> Prop :=
| SCCertLine :
    forall p a mu tau k delta s p' a' k',
      SubCoreT p delta s p' ->
      SubCoreF a delta s a' ->
      SubCoreK k delta s k' ->
      SubCoreCert (CertLine p a mu tau k) delta s (CertLine p' a' mu tau k')
with SubCoreC : Ctx -> Core -> Term -> Ctx -> Prop :=
| SCCNil :
    forall delta s, SubCoreC CtxNil delta s CtxNil
| SCCCons :
    forall line rest delta s line' rest',
      SubCoreCert line delta s line' ->
      SubCoreC rest delta s rest' ->
      SubCoreC (CtxCons line rest) delta s (CtxCons line' rest').

Inductive SubPortF : Frm -> Core -> Frm -> Frm -> Prop :=
| SPFPortHit :
    forall delta b, SubPortF (FPort delta) delta b b
| SPFPortMiss :
    forall epsilon delta b,
      epsilon <> delta ->
      SubPortF (FPort epsilon) delta b (FPort epsilon)
| SPFAtomEq :
    forall s t delta b, SubPortF (FEq s t) delta b (FEq s t)
| SPFAtomRel :
    forall rel ts delta b, SubPortF (FRel rel ts) delta b (FRel rel ts)
| SPFAtomLe :
    forall s t delta b, SubPortF (FLe s t) delta b (FLe s t)
| SPFAtomOwn :
    forall m o t delta b, SubPortF (FOwn m o t) delta b (FOwn m o t)
| SPFNeg :
    forall a delta b a',
      SubPortF a delta b a' ->
      SubPortF (FNeg a) delta b (FNeg a')
| SPFImp :
    forall a c delta b a' c',
      SubPortF a delta b a' ->
      SubPortF c delta b c' ->
      SubPortF (FImp a c) delta b (FImp a' c')
| SPFAllShadow :
    forall d o binder c a delta b,
      term_core d = delta ->
      SubPortF (FAll d o binder c a) delta b (FAll d o binder c a)
| SPFAll :
    forall d o binder c a delta b c' a',
      term_core d <> delta ->
      SubPortC c delta b c' ->
      SubPortF a delta b a' ->
      SubPortF (FAll d o binder c a) delta b (FAll d o binder c' a')
| SPFBeh :
    forall c d epsilon delta b c' d',
      SubPortC c delta b c' ->
      SubPortC d delta b d' ->
      SubPortF (FBeh c d epsilon) delta b (FBeh c' d' epsilon)
with SubPortCert : Cert -> Core -> Frm -> Cert -> Prop :=
| SPCertLine :
    forall p a mu tau k delta b a',
      SubPortF a delta b a' ->
      SubPortCert (CertLine p a mu tau k) delta b (CertLine p a' mu tau k)
with SubPortC : Ctx -> Core -> Frm -> Ctx -> Prop :=
| SPCNil :
    forall delta b, SubPortC CtxNil delta b CtxNil
| SPCCons :
    forall line rest delta b line' rest',
      SubPortCert line delta b line' ->
      SubPortC rest delta b rest' ->
      SubPortC (CtxCons line rest) delta b (CtxCons line' rest').

Record State : Type := {
  state_lookup :> Term -> Core -> option Mode;
  state_finite :
    exists support : list (Term * Core),
      forall a delta m,
        state_lookup a delta = Some m -> In (a, delta) support
}.

Definition StateHas (omega : State) (a : Term) (delta : Core) (m : Mode) : Prop :=
  omega a delta = Some m.

Definition SameExcept (omega omega' : State) (a : Term) (delta : Core) : Prop :=
  forall x e, x <> a \/ e <> delta -> omega' x e = omega x e.

Definition SetTo
    (omega omega' : State) (a : Term) (delta : Core) (m : Mode) : Prop :=
  omega' a delta = Some m /\ SameExcept omega omega' a delta.

Definition RemoveKey
    (omega omega' : State) (a : Term) (delta : Core) : Prop :=
  omega' a delta = None /\ SameExcept omega omega' a delta.

Inductive StepK : State -> KAct -> State -> Prop :=
| StepKNone :
    forall omega, StepK omega KNone omega
| StepKRead :
    forall omega omega' a delta,
      (exists u, StateHas omega u delta MWrite) ->
      SetTo omega omega' a delta MRead ->
      StepK omega (KRead a delta) omega'
| StepKMove :
    forall omega omega1 omega' a b delta,
      StateHas omega a delta MWrite ->
      SetTo omega omega1 a delta MRead ->
      SetTo omega1 omega' b delta MWrite ->
      StepK omega (KMove a b delta) omega'
| StepKCopy :
    forall omega omega' a b delta,
      StateHas omega a delta MWrite ->
      SetTo omega omega' b delta MWrite ->
      StepK omega (KCopy a b delta) omega'
| StepKDrop :
    forall omega omega' a delta,
      StateHas omega a delta MWrite ->
      RemoveKey omega omega' a delta ->
      StepK omega (KDrop a delta) omega'
| StepKSubst :
    forall omega a delta s,
      StateHas omega a delta MWrite ->
      StepK omega (KSubst a delta s) omega.

Inductive StepCtxRaw : Ctx -> State -> State -> Prop :=
| StepCtxRawNil :
    forall omega, StepCtxRaw CtxNil omega omega
| StepCtxRawCons :
    forall line rest omega omega1 omega2 p a mu tau k,
      line = CertLine p a mu tau k ->
      StepK omega k omega1 ->
      StepCtxRaw rest omega1 omega2 ->
      StepCtxRaw (CtxCons line rest) omega omega2.

Definition StepCtx (c : Ctx) (omega omega' : State) : Prop :=
  CtxOK c /\ StepCtxRaw c omega omega'.

Fixpoint ctx_append (c d : Ctx) : Ctx :=
  match c with
  | CtxNil => d
  | CtxCons line rest => CtxCons line (ctx_append rest d)
  end.

Fixpoint HasCopy (c : Ctx) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine _ _ _ _ (KCopy _ _ _)) _ => True
  | CtxCons _ rest => HasCopy rest
  end.

Fixpoint HasDrop (c : Ctx) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine _ _ _ _ (KDrop _ _)) _ => True
  | CtxCons _ rest => HasDrop rest
  end.

Fixpoint ContainsSubst (c : Ctx) (a : Term) (delta : Core) (s : Term) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine _ _ _ _ (KSubst a' delta' s')) rest =>
      (a' = a /\ delta' = delta /\ s' = s) \/ ContainsSubst rest a delta s
  | CtxCons _ rest => ContainsSubst rest a delta s
  end.

Definition OwnSubTerm
    (omega : State) (c : Ctx) (a : Frm) (delta : Core) (s : Term)
    (b : Frm) (omega' : State) : Prop :=
  exists owner,
    ContainsSubst c owner delta s /\
    StateHas omega owner delta MWrite /\
    StepCtx c omega omega' /\
    SubCoreF a delta s b.

Definition OwnSubPort
    (omega : State) (c : Ctx) (a : Frm) (delta : Core) (fragment : Frm)
    (b : Frm) (omega' : State) : Prop :=
  exists owner s,
    ContainsSubst c owner delta s /\
    StateHas omega owner delta MWrite /\
    StepCtx c omega omega' /\
    SubPortF a delta fragment b.

Inductive Forms : State -> Frm -> Prop :=
| FormEq :
    forall omega s t,
      WellTerm s ->
      WellTerm t ->
      Forms omega (FEq s t)
| FormRel :
    forall omega rel ts,
      WellTerms ts ->
      terms_length ts = arR rel ->
      Forms omega (FRel rel ts)
| FormLe :
    forall omega s t,
      WellTerm s ->
      WellTerm t ->
      Forms omega (FLe s t)
| FormOwn :
    forall omega m o t,
      WellTerm o ->
      WellTerm t ->
      Forms omega (FOwn m o t)
| FormPort :
    forall omega delta, Forms omega (FPort delta)
| FormNeg :
    forall omega a, Forms omega a -> Forms omega (FNeg a)
| FormImp :
    forall omega a b, Forms omega a -> Forms omega b -> Forms omega (FImp a b)
| FormAll :
    forall omega omega' d o b c a xi,
      WellTerm d ->
      WellTerm o ->
      WellTerm b ->
      WellFrm a ->
      NameOK (FAll d o b c a) ->
      term_core d = vcore xi ->
      StateHas omega o (term_core d) MWrite ->
      CtxOK c ->
      StepCtx c omega omega' ->
      StateHas omega' o (term_core d) MRead ->
      StateHas omega' b (term_core d) MWrite ->
      Forms omega' a ->
      Forms omega (FAll d o b c a)
| FormBeh :
    forall omega c d delta,
      CtxOK c ->
      CtxOK d ->
      Forms omega (FBeh c d delta).

Inductive OrdRel : Type :=
| OrdBase : R -> OrdRel
| OrdLe
| OrdOwn : Mode -> OrdRel
| OrdPort : Core -> OrdRel
| OrdBeh : Core -> OrdRel.

Inductive OrdTerm : Type :=
| OVar : Name -> OrdTerm
| OConstOwn : Own -> OrdTerm
| OConstNat : nat -> OrdTerm
| OPair : OrdTerm -> OrdTerm -> OrdTerm
| OOp : G -> OrdTerms -> OrdTerm
with OrdTerms : Type :=
| OTermsNil : OrdTerms
| OTermsCons : OrdTerm -> OrdTerms -> OrdTerms.

Inductive OrdFrm : Type :=
| OEq : OrdTerm -> OrdTerm -> OrdFrm
| ORel : OrdRel -> OrdTerms -> OrdFrm
| ONeg : OrdFrm -> OrdFrm
| OImp : OrdFrm -> OrdFrm -> OrdFrm
| OAll : Name -> OrdFrm -> OrdFrm.

Fixpoint in_ord_terms (x : Name) (ts : OrdTerms) : Prop :=
  match ts with
  | OTermsNil => False
  | OTermsCons t rest => in_ord_term x t \/ in_ord_terms x rest
  end
with in_ord_term (x : Name) (t : OrdTerm) : Prop :=
  match t with
  | OVar y => x = y
  | OConstOwn _ => False
  | OConstNat _ => False
  | OPair s u => in_ord_term x s \/ in_ord_term x u
  | OOp _ ts => in_ord_terms x ts
  end.

Fixpoint in_ord_frm (x : Name) (a : OrdFrm) : Prop :=
  match a with
  | OEq s t => in_ord_term x s \/ in_ord_term x t
  | ORel _ ts => in_ord_terms x ts
  | ONeg b => in_ord_frm x b
  | OImp b c => in_ord_frm x b \/ in_ord_frm x c
  | OAll y b => x <> y /\ in_ord_frm x b
  end.

Fixpoint ord_terms_subst (ts : OrdTerms) (x : Name) (s : OrdTerm) : OrdTerms :=
  match ts with
  | OTermsNil => OTermsNil
  | OTermsCons t rest => OTermsCons (ord_term_subst t x s) (ord_terms_subst rest x s)
  end
with ord_term_subst (t : OrdTerm) (x : Name) (s : OrdTerm) : OrdTerm :=
  match t with
  | OVar y => if Nat.eq_dec y x then s else OVar y
  | OConstOwn o => OConstOwn o
  | OConstNat n => OConstNat n
  | OPair u v => OPair (ord_term_subst u x s) (ord_term_subst v x s)
  | OOp g ts => OOp g (ord_terms_subst ts x s)
  end.

Fixpoint fv_ord_terms_list (ts : OrdTerms) : list Name :=
  match ts with
  | OTermsNil => []
  | OTermsCons t rest => fv_ord_term_list t ++ fv_ord_terms_list rest
  end
with fv_ord_term_list (t : OrdTerm) : list Name :=
  match t with
  | OVar x => [x]
  | OConstOwn _ => []
  | OConstNat _ => []
  | OPair s u => fv_ord_term_list s ++ fv_ord_term_list u
  | OOp _ ts => fv_ord_terms_list ts
  end.

Fixpoint fv_ord_frm_list (a : OrdFrm) : list Name :=
  match a with
  | OEq s t => fv_ord_term_list s ++ fv_ord_term_list t
  | ORel _ ts => fv_ord_terms_list ts
  | ONeg b => fv_ord_frm_list b
  | OImp b c => fv_ord_frm_list b ++ fv_ord_frm_list c
  | OAll x b => remove Nat.eq_dec x (fv_ord_frm_list b)
  end.

Fixpoint names_ord_terms_list (ts : OrdTerms) : list Name :=
  match ts with
  | OTermsNil => []
  | OTermsCons t rest => names_ord_term_list t ++ names_ord_terms_list rest
  end
with names_ord_term_list (t : OrdTerm) : list Name :=
  match t with
  | OVar x => [x]
  | OConstOwn _ => []
  | OConstNat _ => []
  | OPair s u => names_ord_term_list s ++ names_ord_term_list u
  | OOp _ ts => names_ord_terms_list ts
  end.

Fixpoint names_ord_frm_list (a : OrdFrm) : list Name :=
  match a with
  | OEq s t => names_ord_term_list s ++ names_ord_term_list t
  | ORel _ ts => names_ord_terms_list ts
  | ONeg b => names_ord_frm_list b
  | OImp b c => names_ord_frm_list b ++ names_ord_frm_list c
  | OAll x b => x :: names_ord_frm_list b
  end.

Fixpoint ord_terms_size (ts : OrdTerms) : nat :=
  match ts with
  | OTermsNil => 0
  | OTermsCons t rest => ord_term_size t + ord_terms_size rest
  end
with ord_term_size (t : OrdTerm) : nat :=
  match t with
  | OVar _ => 1
  | OConstOwn _ => 1
  | OConstNat _ => 1
  | OPair s u => S (ord_term_size s + ord_term_size u)
  | OOp _ ts => S (ord_terms_size ts)
  end.

Fixpoint ord_frm_size (a : OrdFrm) : nat :=
  match a with
  | OEq s t => S (ord_term_size s + ord_term_size t)
  | ORel _ ts => S (ord_terms_size ts)
  | ONeg b => S (ord_frm_size b)
  | OImp b c => S (ord_frm_size b + ord_frm_size c)
  | OAll _ b => S (ord_frm_size b)
  end.

Fixpoint ord_terms_rename_var (ts : OrdTerms) (old new : Name) : OrdTerms :=
  match ts with
  | OTermsNil => OTermsNil
  | OTermsCons t rest =>
      OTermsCons (ord_term_rename_var t old new)
        (ord_terms_rename_var rest old new)
  end
with ord_term_rename_var (t : OrdTerm) (old new : Name) : OrdTerm :=
  match t with
  | OVar y => if Nat.eq_dec y old then OVar new else OVar y
  | OConstOwn o => OConstOwn o
  | OConstNat n => OConstNat n
  | OPair u v =>
      OPair (ord_term_rename_var u old new) (ord_term_rename_var v old new)
  | OOp g ts => OOp g (ord_terms_rename_var ts old new)
  end.

Fixpoint ord_frm_rename_var (a : OrdFrm) (old new : Name) : OrdFrm :=
  match a with
  | OEq u v => OEq (ord_term_rename_var u old new) (ord_term_rename_var v old new)
  | ORel rel ts => ORel rel (ord_terms_rename_var ts old new)
  | ONeg b => ONeg (ord_frm_rename_var b old new)
  | OImp b c => OImp (ord_frm_rename_var b old new) (ord_frm_rename_var c old new)
  | OAll y b =>
      if Nat.eq_dec y old then OAll y b
      else OAll y (ord_frm_rename_var b old new)
  end.

Fixpoint ord_terms_rename_size
    (ts : OrdTerms) (old new : Name) {struct ts}
    : ord_terms_size (ord_terms_rename_var ts old new) = ord_terms_size ts
with ord_term_rename_size
    (t : OrdTerm) (old new : Name) {struct t}
    : ord_term_size (ord_term_rename_var t old new) = ord_term_size t.
Proof.
  - destruct ts as [| t rest].
    + reflexivity.
    + simpl.
      rewrite ord_term_rename_size.
      rewrite ord_terms_rename_size.
      reflexivity.
  - destruct t as [y | o | n | u v | g ts].
    + simpl. destruct (Nat.eq_dec y old); reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl.
      rewrite ord_term_rename_size.
      rewrite ord_term_rename_size.
      reflexivity.
    + simpl.
      rewrite ord_terms_rename_size.
      reflexivity.
Qed.

Fixpoint ord_frm_rename_size
    (a : OrdFrm) (old new : Name) {struct a}
    : ord_frm_size (ord_frm_rename_var a old new) = ord_frm_size a.
Proof.
  destruct a as [s t | rel ts | b | b c | y b].
  - simpl.
    rewrite ord_term_rename_size.
    rewrite ord_term_rename_size.
    reflexivity.
  - simpl.
    rewrite ord_terms_rename_size.
    reflexivity.
  - simpl.
    rewrite ord_frm_rename_size.
    reflexivity.
  - simpl.
    rewrite ord_frm_rename_size.
    rewrite ord_frm_rename_size.
    reflexivity.
  - simpl.
    destruct (Nat.eq_dec y old).
    + reflexivity.
    + simpl.
      rewrite ord_frm_rename_size.
      reflexivity.
Qed.

Definition Renaming := Name -> Name.

Definition ren_id : Renaming := fun x => x.

Definition ren_extend (rho : Renaming) (old new : Name) : Renaming :=
  fun x => if Nat.eq_dec x old then new else rho x.

Definition ren_shadow (rho : Renaming) (x : Name) : Renaming :=
  fun y => if Nat.eq_dec y x then x else rho y.

Fixpoint ord_terms_rename_env (ts : OrdTerms) (rho : Renaming) : OrdTerms :=
  match ts with
  | OTermsNil => OTermsNil
  | OTermsCons t rest =>
      OTermsCons (ord_term_rename_env t rho) (ord_terms_rename_env rest rho)
  end
with ord_term_rename_env (t : OrdTerm) (rho : Renaming) : OrdTerm :=
  match t with
  | OVar x => OVar (rho x)
  | OConstOwn o => OConstOwn o
  | OConstNat n => OConstNat n
  | OPair s u => OPair (ord_term_rename_env s rho) (ord_term_rename_env u rho)
  | OOp g ts => OOp g (ord_terms_rename_env ts rho)
  end.

Fixpoint ord_frm_rename_env (a : OrdFrm) (rho : Renaming) : OrdFrm :=
  match a with
  | OEq s t => OEq (ord_term_rename_env s rho) (ord_term_rename_env t rho)
  | ORel rel ts => ORel rel (ord_terms_rename_env ts rho)
  | ONeg b => ONeg (ord_frm_rename_env b rho)
  | OImp b c => OImp (ord_frm_rename_env b rho) (ord_frm_rename_env c rho)
  | OAll x b => OAll (rho x) (ord_frm_rename_env b rho)
  end.

Fixpoint names_ord_terms_rename_env_list
    (ts : OrdTerms) (rho : Renaming) : list Name :=
  match ts with
  | OTermsNil => []
  | OTermsCons t rest =>
      names_ord_term_rename_env_list t rho ++
      names_ord_terms_rename_env_list rest rho
  end
with names_ord_term_rename_env_list
    (t : OrdTerm) (rho : Renaming) : list Name :=
  match t with
  | OVar x => [rho x]
  | OConstOwn _ => []
  | OConstNat _ => []
  | OPair s u =>
      names_ord_term_rename_env_list s rho ++
      names_ord_term_rename_env_list u rho
  | OOp _ ts => names_ord_terms_rename_env_list ts rho
  end.

Fixpoint names_ord_frm_rename_env_list
    (a : OrdFrm) (rho : Renaming) : list Name :=
  match a with
  | OEq s t =>
      names_ord_term_rename_env_list s rho ++
      names_ord_term_rename_env_list t rho
  | ORel _ ts => names_ord_terms_rename_env_list ts rho
  | ONeg b => names_ord_frm_rename_env_list b rho
  | OImp b c =>
      names_ord_frm_rename_env_list b rho ++
      names_ord_frm_rename_env_list c rho
  | OAll x b => rho x :: names_ord_frm_rename_env_list b rho
  end.

Fixpoint ord_terms_subst_env
    (ts : OrdTerms) (rho : Renaming) (x : Name) (s : OrdTerm) : OrdTerms :=
  match ts with
  | OTermsNil => OTermsNil
  | OTermsCons t rest =>
      OTermsCons (ord_term_subst_env t rho x s)
        (ord_terms_subst_env rest rho x s)
  end
with ord_term_subst_env
    (t : OrdTerm) (rho : Renaming) (x : Name) (s : OrdTerm) : OrdTerm :=
  match t with
  | OVar y =>
      let y' := rho y in
      if Nat.eq_dec y' x then s else OVar y'
  | OConstOwn o => OConstOwn o
  | OConstNat n => OConstNat n
  | OPair u v =>
      OPair (ord_term_subst_env u rho x s) (ord_term_subst_env v rho x s)
  | OOp g ts => OOp g (ord_terms_subst_env ts rho x s)
  end.

Fixpoint ord_frm_subst_env
    (a : OrdFrm) (rho : Renaming) (x : Name) (s : OrdTerm) : OrdFrm :=
  match a with
  | OEq u v =>
      OEq (ord_term_subst_env u rho x s) (ord_term_subst_env v rho x s)
  | ORel rel ts => ORel rel (ord_terms_subst_env ts rho x s)
  | ONeg b => ONeg (ord_frm_subst_env b rho x s)
  | OImp b c =>
      OImp (ord_frm_subst_env b rho x s) (ord_frm_subst_env c rho x s)
  | OAll y b =>
      let rho_body := ren_shadow rho y in
      if Nat.eq_dec y x then
        OAll y (ord_frm_rename_env b rho_body)
      else if in_dec Nat.eq_dec y (fv_ord_term_list s) then
        let z :=
          freshName
            (names_ord_frm_rename_env_list b rho_body ++
             fv_ord_term_list s ++ [x; y]) in
        OAll z (ord_frm_subst_env b (ren_extend rho_body y z) x s)
      else
        OAll y (ord_frm_subst_env b rho_body x s)
  end.

Definition ord_frm_subst (a : OrdFrm) (x : Name) (s : OrdTerm) : OrdFrm :=
  ord_frm_subst_env a ren_id x s.

Fixpoint forget_terms (ts : Terms) : OrdTerms :=
  match ts with
  | TNil => OTermsNil
  | TCons t rest => OTermsCons (forget_term t) (forget_terms rest)
  end
with forget_term (t : Term) : OrdTerm :=
  match t with
  | TVar x _ => OVar x
  | TOwner o => OConstOwn o
  | TPath r _ _ => OConstNat r
  | TComp a b => OPair (forget_term a) (forget_term b)
  | TOp g ts => OOp g (forget_terms ts)
  | TDecl _ u => forget_term u
  | TQuote _ => OConstNat 0
  end.

Fixpoint forget_frm (a : Frm) : OrdFrm :=
  match a with
  | FEq s t => OEq (forget_term s) (forget_term t)
  | FRel rel ts => ORel (OrdBase rel) (forget_terms ts)
  | FLe s t => ORel OrdLe (OTermsCons (forget_term s) (OTermsCons (forget_term t) OTermsNil))
  | FOwn m o t => ORel (OrdOwn m) (OTermsCons (forget_term o) (OTermsCons (forget_term t) OTermsNil))
  | FPort delta => ORel (OrdPort delta) OTermsNil
  | FNeg b => ONeg (forget_frm b)
  | FImp b c => OImp (forget_frm b) (forget_frm c)
  | FAll d _ _ _ b =>
      let xd :=
        match d with
        | TVar x _ => x
        | _ => freshName (fv_ord_frm_list (forget_frm b))
        end in
      OAll xd (forget_frm b)
  | FBeh _ _ delta => ORel (OrdBeh delta) OTermsNil
  end.

Definition OrdAlphaClosed (e : OrdFrm -> OrdFrm -> Prop) : Prop :=
  Equivalence e /\
  (forall s t s' t', s = s' -> t = t' -> e (OEq s t) (OEq s' t')) /\
  (forall rel ts ts', ts = ts' -> e (ORel rel ts) (ORel rel ts')) /\
  (forall a b, e a b -> e (ONeg a) (ONeg b)) /\
  (forall a0 b0 a1 b1,
    e a0 b0 -> e a1 b1 -> e (OImp a0 a1) (OImp b0 b1)) /\
  (forall x a b, e a b -> e (OAll x a) (OAll x b)) /\
  (forall x y a,
    ~ (in_ord_frm y a /\ x <> y) ->
    e (OAll x a) (OAll y (ord_frm_subst a x (OVar y)))).

Definition OrdAlpha (a b : OrdFrm) : Prop :=
  forall e, OrdAlphaClosed e -> e a b.

Lemma OrdAlpha_equiv : Equivalence OrdAlpha.
Proof.
  unfold OrdAlpha, OrdAlphaClosed.
  split.
  - intros a e He.
    destruct He as [Heq _].
    destruct Heq as [Href _ _].
    exact (Href a).
  - intros a b Hab e He.
    pose proof (Hab e He) as Hab_e.
    destruct He as [Heq _].
    destruct Heq as [_ Hsym _].
    exact (Hsym a b Hab_e).
  - intros a b c Hab Hbc e He.
    pose proof (Hab e He) as Hab_e.
    pose proof (Hbc e He) as Hbc_e.
    destruct He as [Heq _].
    destruct Heq as [_ _ Htrans].
    exact (Htrans a b c Hab_e Hbc_e).
Qed.

Definition Library := Ctx -> Prop.

Definition FiniteLibrary (k : Library) : Prop :=
  exists support : list Ctx, forall c, k c -> In c support.

Definition Hat (k : Library) (c : Ctx) : Prop :=
  forall l : Library,
    (forall c0, k c0 -> l c0) ->
    (forall c0 d0, l c0 -> l d0 -> CtxOK (ctx_append c0 d0) -> l (ctx_append c0 d0)) ->
    l c.

Lemma Hat_base :
  forall k c, k c -> Hat k c.
Proof.
  unfold Hat. intros k c H l Hbase _. exact (Hbase c H).
Qed.

Lemma Hat_append :
  forall k c d,
    Hat k c ->
    Hat k d ->
    CtxOK (ctx_append c d) ->
    Hat k (ctx_append c d).
Proof.
  unfold Hat.
  intros k c d Hc Hd Hok l Hbase Hclosed.
  apply Hclosed; [apply Hc | apply Hd | exact Hok]; assumption.
Qed.

Definition StateFrm := (State * Frm)%type.

Definition SF (p : StateFrm) : Prop :=
  Forms (fst p) (snd p).

Definition SubsetSF (x : SetOf StateFrm) : Prop :=
  forall p, x p -> SF p.

Definition StateWeakens (omega0 omega : State) : Prop :=
  (forall a delta m, omega0 a delta = Some m -> omega a delta = Some m) /\
  (forall a delta, omega0 a delta = None ->
     omega a delta = None \/ omega a delta = Some MRead).

Inductive GammaMinus (k : Library) (x : SetOf StateFrm) : StateFrm -> Prop :=
| GMKeep :
    forall p,
      x p ->
      SF p ->
      GammaMinus k x p
| GMWaken :
    forall omega0 omega a,
      x (omega0, a) ->
      StateWeakens omega0 omega ->
      SF (omega, a) ->
      GammaMinus k x (omega, a)
| GMEnterAll :
    forall omega0 omega d o b c body,
      x (omega0, FAll d o b c body) ->
      StepCtx c omega0 omega ->
      SF (omega, body) ->
      GammaMinus k x (omega, body)
| GMCopy :
    forall omega0 omega a c,
      x (omega0, a) ->
      Hat k c ->
      StepCtx c omega0 omega ->
      HasCopy c ->
      SF (omega, a) ->
      GammaMinus k x (omega, a)
| GMDrop :
    forall omega0 omega a c,
      x (omega0, a) ->
      Hat k c ->
      StepCtx c omega0 omega ->
      HasDrop c ->
      SF (omega, a) ->
      GammaMinus k x (omega, a)
| GMSubTerm :
    forall omega0 omega a0 a c delta s,
      x (omega0, a0) ->
      Hat k c ->
      OwnSubTerm omega0 c a0 delta s a omega ->
      SF (omega, a) ->
      GammaMinus k x (omega, a)
| GMSubPort :
    forall omega0 omega a0 a c delta fragment,
      x (omega0, a0) ->
      Hat k c ->
      OwnSubPort omega0 c a0 delta fragment a omega ->
      SF (omega, a) ->
      GammaMinus k x (omega, a).

Definition ClosedMinus (k : Library) (x : SetOf StateFrm) : Prop :=
  SubsetSF x /\
  forall p, GammaMinus k x p -> x p.

Definition ClMinus (k : Library) (omega : State) (a : Frm) : SetOf StateFrm :=
  fun p =>
    SF (omega, a) /\
    SF p /\
    forall x : SetOf StateFrm,
      SubsetSF x ->
      x (omega, a) ->
      ClosedMinus k x ->
      x p.

Definition ResMinus
    (delta : Core) (k : Library) (omega : State) (a : Frm) : SetOf StateFrm :=
  fun p =>
    SF (omega, a) /\
    SF p /\
    exists omega' a' c s,
      ClMinus k omega a (omega', a') /\
      Hat k c /\
      OwnSubTerm omega' c a' delta s (snd p) (fst p).

Definition lib_add (k : Library) (c : Ctx) : Library :=
  fun d => k d \/ d = c.

Definition BehEq (c d : Ctx) (delta : Core) : Prop :=
  forall k omega a p,
    FiniteLibrary k ->
    SF (omega, a) ->
    SF p ->
    ResMinus delta (lib_add k c) omega a p <->
    ResMinus delta (lib_add k d) omega a p.

Definition OwnAlphaClosed (e : Frm -> Frm -> Prop) : Prop :=
  Equivalence e /\
  (forall a b, fshape a = fshape b ->
    (match a, b with
     | FEq _ _, FEq _ _
     | FRel _ _, FRel _ _
     | FLe _ _, FLe _ _
     | FOwn _ _ _, FOwn _ _ _
     | FPort _, FPort _ => True
     | _, _ => False
     end) ->
    e a b) /\
  (forall c0 c1 d0 d1 delta,
    BehEq c0 c1 delta ->
    BehEq d0 d1 delta ->
    e (FBeh c0 d0 delta) (FBeh c1 d1 delta)) /\
  (forall a b, e a b -> e (FNeg a) (FNeg b)) /\
  (forall a0 b0 a1 b1, e a0 b0 -> e a1 b1 -> e (FImp a0 a1) (FImp b0 b1)) /\
  (forall d e0 o o' b b' c0 c1 a0 a1,
    e a0 a1 ->
    term_core d = term_core e0 ->
    term_core o = term_core o' ->
    term_core b = term_core b' ->
    BehEq c0 c1 (term_core d) ->
    e (FAll d o b c0 a0) (FAll e0 o' b' c1 a1)).

Definition OwnAlphaRaw (a b : Frm) : Prop :=
  forall e, OwnAlphaClosed e -> e a b.

Definition OwnAlpha (a b : Frm) : Prop :=
  OwnAlphaRaw a b /\ OrdAlpha (forget_frm a) (forget_frm b).

Lemma OwnAlphaRaw_sym :
  forall a b, OwnAlphaRaw a b -> OwnAlphaRaw b a.
Proof.
  unfold OwnAlphaRaw, OwnAlphaClosed.
  intros a b Hab e He.
  pose proof (Hab e He) as Hab_e.
  destruct He as [Heq _].
  destruct Heq as [_ Hsym _].
  apply Hsym.
  exact Hab_e.
Qed.

Lemma OwnAlpha_sym :
  forall a b, OwnAlpha a b -> OwnAlpha b a.
Proof.
  intros a b [Hraw Hord].
  split.
  - apply OwnAlphaRaw_sym. exact Hraw.
  - destruct OrdAlpha_equiv as [_ Hsym _]. now apply Hsym.
Qed.

Inductive GammaFull (k : Library) (x : SetOf StateFrm) : StateFrm -> Prop :=
| GFullMinus :
    forall p,
      GammaMinus k x p ->
      SF p ->
      GammaFull k x p
| GFullAlpha :
    forall omega a b,
      x (omega, a) ->
      OwnAlpha a b ->
      SF (omega, b) ->
      GammaFull k x (omega, b).

Definition ClosedFull (k : Library) (x : SetOf StateFrm) : Prop :=
  SubsetSF x /\
  forall p, GammaFull k x p -> x p.

Definition Cl (k : Library) (omega : State) (a : Frm) : SetOf StateFrm :=
  fun p =>
    SF (omega, a) /\
    SF p /\
    forall x : SetOf StateFrm,
      SubsetSF x ->
      x (omega, a) ->
      ClosedFull k x ->
      x p.

Definition Res
    (delta : Core) (k : Library) (omega : State) (a : Frm) : SetOf StateFrm :=
  fun p =>
    SF (omega, a) /\
    SF p /\
    exists omega' a' c s,
      Cl k omega a (omega', a') /\
      Hat k c /\
      OwnSubTerm omega' c a' delta s (snd p) (fst p).

Definition ClEq (k : Library) (omega : State) (a b : Frm) : Prop :=
  forall p, Cl k omega a p <-> Cl k omega b p.

Inductive GammaFullOrdAlpha (k : Library) (x : SetOf StateFrm) : StateFrm -> Prop :=
| GFullOrdMinus :
    forall p,
      GammaMinus k x p ->
      SF p ->
      GammaFullOrdAlpha k x p
| GFullOrdAlpha :
    forall omega a b,
      x (omega, a) ->
      OrdAlpha (forget_frm a) (forget_frm b) ->
      SF (omega, b) ->
      GammaFullOrdAlpha k x (omega, b).

Definition ClosedFullOrdAlpha (k : Library) (x : SetOf StateFrm) : Prop :=
  SubsetSF x /\
  forall p, GammaFullOrdAlpha k x p -> x p.

Definition ClOrdAlpha (k : Library) (omega : State) (a : Frm) : SetOf StateFrm :=
  fun p =>
    SF (omega, a) /\
    SF p /\
    forall x : SetOf StateFrm,
      SubsetSF x ->
      x (omega, a) ->
      ClosedFullOrdAlpha k x ->
      x p.

Definition ClEqOrdAlpha (k : Library) (omega : State) (a b : Frm) : Prop :=
  forall p, ClOrdAlpha k omega a p <-> ClOrdAlpha k omega b p.

Definition ClosureDifferentOrdAlpha (k : Library) (omega : State) (a b : Frm) : Prop :=
  ~ ClEqOrdAlpha k omega a b.

Lemma closed_alpha_member :
  forall k x omega a b,
    ClosedFull k x ->
    x (omega, a) ->
    OwnAlpha a b ->
    SF (omega, b) ->
    x (omega, b).
Proof.
  intros k x omega a b [_ Hclosed] Hx Halpha Hsf.
  apply Hclosed.
  apply GFullAlpha with (a := a); assumption.
Qed.

Lemma closed_ord_alpha_member :
  forall k x omega a b,
    ClosedFullOrdAlpha k x ->
    x (omega, a) ->
    OrdAlpha (forget_frm a) (forget_frm b) ->
    SF (omega, b) ->
    x (omega, b).
Proof.
  intros k x omega a b [_ Hclosed] Hx Halpha Hsf.
  apply Hclosed.
  apply GFullOrdAlpha with (a := a); assumption.
Qed.

Theorem cl_ord_alpha_invariant :
  forall k omega a b,
    FiniteLibrary k ->
    SF (omega, a) ->
    SF (omega, b) ->
    OrdAlpha (forget_frm a) (forget_frm b) ->
    ClEqOrdAlpha k omega a b.
Proof.
  unfold ClEqOrdAlpha, ClOrdAlpha.
  intros k omega a b _ Hsfa Hsfb Hab p.
  split; intros [_ [Hsf_p Hcl]].
  - split; [exact Hsfb |].
    split; [exact Hsf_p |].
    intros x Hx_sf Hx Hclosed.
    apply Hcl; [exact Hx_sf | | exact Hclosed].
    destruct OrdAlpha_equiv as [_ Hsym _].
    exact (closed_ord_alpha_member k x omega b a Hclosed Hx (Hsym _ _ Hab) Hsfa).
  - split; [exact Hsfa |].
    split; [exact Hsf_p |].
    intros x Hx_sf Hx Hclosed.
    apply Hcl; [exact Hx_sf | | exact Hclosed].
    exact (closed_ord_alpha_member k x omega a b Hclosed Hx Hab Hsfb).
Qed.

Theorem cl_alpha_invariant :
  forall k omega a b,
    FiniteLibrary k ->
    SF (omega, a) ->
    SF (omega, b) ->
    OwnAlpha a b ->
    ClEq k omega a b.
Proof.
  unfold ClEq, Cl.
  intros k omega a b _ Hsfa Hsfb Hab p.
  split; intros [_ [Hsf_p Hcl]].
  - split; [exact Hsfb |].
    split; [exact Hsf_p |].
    intros x Hx_sf Hx Hclosed.
    apply Hcl; [exact Hx_sf | | exact Hclosed].
    exact (closed_alpha_member k x omega b a Hclosed Hx (OwnAlpha_sym a b Hab) Hsfa).
  - split; [exact Hsfa |].
    split; [exact Hsf_p |].
    intros x Hx_sf Hx Hclosed.
    apply Hcl; [exact Hx_sf | | exact Hclosed].
    exact (closed_alpha_member k x omega a b Hclosed Hx Hab Hsfb).
Qed.

Inductive Ax (omega : State) : Frm -> Prop :=
| AxImp1 :
    forall a b,
      Forms omega a ->
      Forms omega b ->
      Ax omega (FImp a (FImp b a))
| AxImp2 :
    forall a b c,
      Forms omega a ->
      Forms omega b ->
      Forms omega c ->
      Ax omega
        (FImp (FImp a (FImp b c))
          (FImp (FImp a b) (FImp a c)))
| AxImp3 :
    forall a b,
      Forms omega a ->
      Forms omega b ->
      Ax omega (FImp (FImp (FNeg a) (FNeg b)) (FImp b a))
| AxEqRefl :
    forall t,
      WellTerm t ->
      Ax omega (FEq t t)
| AxEqSubst :
    forall s t a delta asub tsub,
      WellTerm s ->
      WellTerm t ->
      Forms omega a ->
      Forms omega asub ->
      Forms omega tsub ->
      SubCoreF a delta s asub ->
      SubCoreF a delta t tsub ->
      Ax omega (FImp (FEq s t) (FImp asub tsub))
| AxAllInst :
    forall d o b c a s asub,
      WellTerm s ->
      Forms omega (FAll d o b c a) ->
      Forms omega asub ->
      SubCoreF a (term_core d) s asub ->
      Ax omega (FImp (FAll d o b c a) asub)
| AxBehRefl :
    forall c delta,
      CtxOK c ->
      Ax omega (FBeh c c delta)
| AxWriteRead :
    forall o t,
      WellTerm o ->
      WellTerm t ->
      Ax omega (FImp (FOwn MWrite o t) (FOwn MRead o t)).

Inductive RuleO : list StateFrm -> StateFrm -> Prop :=
| RuleMP :
    forall omega a b,
      Forms omega a ->
      Forms omega b ->
      RuleO [(omega, a); (omega, FImp a b)] (omega, b)
| RuleAllIntro :
    forall omega omega' d o b c a xi,
      WellTerm d ->
      WellTerm o ->
      WellTerm b ->
      CtxOK c ->
      term_core d = vcore xi ->
      NameOK (FAll d o b c a) ->
      StateHas omega o (term_core d) MWrite ->
      StepCtx c omega omega' ->
      StateHas omega' o (term_core d) MRead ->
      StateHas omega' b (term_core d) MWrite ->
      Forms omega' a ->
      RuleO [(omega', a)] (omega, FAll d o b c a)
| RuleSubTerm :
    forall omega omega' a b c delta s,
      Forms omega a ->
      Forms omega' b ->
      OwnSubTerm omega c a delta s b omega' ->
      RuleO [(omega, a)] (omega', b)
| RuleSubPort :
    forall omega omega' a b c delta fragment,
      Forms omega a ->
      Forms omega' b ->
      OwnSubPort omega c a delta fragment b omega' ->
      RuleO [(omega, a)] (omega', b)
| RuleAlpha :
    forall omega a b,
      OwnAlpha a b ->
      Forms omega a ->
      Forms omega b ->
      RuleO [(omega, a)] (omega, b).

Inductive Derives (gamma : SetOf StateFrm) : StateFrm -> Prop :=
| DerAssumption :
    forall p, gamma p -> Derives gamma p
| DerAxiom :
    forall omega a, Ax omega a -> Derives gamma (omega, a)
| DerModusPonens :
    forall omega a b,
      Derives gamma (omega, a) ->
      Derives gamma (omega, FImp a b) ->
      Derives gamma (omega, b)
| DerRule :
    forall premises q,
      (forall p, In p premises -> Derives gamma p) ->
      RuleO premises q ->
      Derives gamma q.

Definition ThmO (p : StateFrm) : Prop :=
  SF p /\ Derives (fun _ => False) p.

Record Model : Type := {
  carrier : Type;
  carrier_inhabited : inhabited carrier;
  interp_g : G -> list carrier -> carrier;
  interp_r : R -> list carrier -> Prop;
  preceq : carrier -> carrier -> Prop;
  preceq_refl : forall x, preceq x x;
  preceq_trans : forall x y z, preceq x y -> preceq y z -> preceq x z;
  interp_path : nat -> carrier -> carrier -> carrier;
  interp_comp : carrier -> carrier -> carrier;
  interp_quote : Ctx -> carrier;
  interp_bind : carrier -> carrier -> carrier;
  interp_owner : Own -> carrier
}.

Fixpoint interp_term
    (m : Model) (nu : Obj -> carrier m) (t : Term) {struct t}
    : carrier m :=
  match t with
  | TVar _ xi => nu xi
  | TOwner o => interp_owner m o
  | TPath r a b => interp_path m r (interp_term m nu a) (interp_term m nu b)
  | TComp p q => interp_comp m (interp_term m nu p) (interp_term m nu q)
  | TOp g ts => interp_g m g (interp_terms m nu ts)
  | TDecl d u => interp_bind m (interp_term m nu d) (interp_term m nu u)
  | TQuote c => interp_quote m c
  end
with interp_terms
    (m : Model) (nu : Obj -> carrier m) (ts : Terms) {struct ts}
    : list (carrier m) :=
  match ts with
  | TNil => []
  | TCons t rest => interp_term m nu t :: interp_terms m nu rest
  end.

Definition PortVal := Core -> option bool.

Definition Rebinds
    (m : Model) (nu nu' : Obj -> carrier m) (delta : Core) (x : carrier m)
    : Prop :=
  (forall xi, vcore xi = delta -> nu' xi = x) /\
  (forall xi, vcore xi <> delta -> nu' xi = nu xi).

Fixpoint Satisfies
    (m : Model) (nu : Obj -> carrier m) (rho : PortVal)
    (omega : State) (a : Frm) {struct a} : Prop :=
  Forms omega a /\
  match a with
  | FEq s t => interp_term m nu s = interp_term m nu t
  | FRel rel ts => interp_r m rel (interp_terms m nu ts)
  | FLe s t => preceq m (interp_term m nu s) (interp_term m nu t)
  | FOwn mode o t => StateHas omega o (term_core t) mode
  | FPort delta => rho delta = Some true
  | FNeg b => ~ Satisfies m nu rho omega b
  | FImp b c => ~ Satisfies m nu rho omega b \/ Satisfies m nu rho omega c
  | FAll d _ _ c body =>
      exists omega',
        StepCtx c omega omega' /\
        forall x nu',
          Rebinds m nu nu' (term_core d) x ->
          Satisfies m nu' rho omega' body
  | FBeh c d delta => BehEq c d delta
  end.

Definition empty_state : State.
Proof.
  refine {| state_lookup := fun _ _ => None |}.
  exists []. intros a delta mode H. discriminate.
Defined.

Definition unit_ownership_model : Model := {|
  carrier := unit;
  carrier_inhabited := inhabits tt;
  interp_g := fun _ _ => tt;
  interp_r := fun _ _ => False;
  preceq := fun _ _ => True;
  preceq_refl := fun _ => I;
  preceq_trans := fun _ _ _ _ _ => I;
  interp_path := fun _ _ _ => tt;
  interp_comp := fun _ _ => tt;
  interp_quote := fun _ => tt;
  interp_bind := fun _ _ => tt;
  interp_owner := fun _ => tt
|}.

Definition unit_object_environment :
    Obj -> carrier unit_ownership_model := fun _ => tt.

Definition empty_port_valuation : PortVal := fun _ => None.

Definition reflexive_owner_equality : Frm :=
  FEq (TOwner 0) (TOwner 0).

Lemma unit_model_satisfies_reflexive_owner_equality :
  Satisfies unit_ownership_model unit_object_environment
    empty_port_valuation empty_state reflexive_owner_equality.
Proof.
  split.
  - unfold reflexive_owner_equality. constructor; constructor.
  - reflexivity.
Qed.

Lemma unit_model_refutes_negated_reflexive_owner_equality :
  ~ Satisfies unit_ownership_model unit_object_environment
      empty_port_valuation empty_state (FNeg reflexive_owner_equality).
Proof.
  intros [_ Hneg].
  apply Hneg.
  exact unit_model_satisfies_reflexive_owner_equality.
Qed.

Theorem ownership_semantics_nontrivial :
  exists m : Model,
  exists nu : Obj -> carrier m,
  exists rho : PortVal,
  exists omega : State,
    Satisfies m nu rho omega reflexive_owner_equality /\
    ~ Satisfies m nu rho omega (FNeg reflexive_owner_equality).
Proof.
  exists unit_ownership_model, unit_object_environment,
    empty_port_valuation, empty_state.
  split.
  - exact unit_model_satisfies_reflexive_owner_equality.
  - exact unit_model_refutes_negated_reflexive_owner_equality.
Qed.

Definition SemEntails (gamma : SetOf StateFrm) (omega : State) (a : Frm) : Prop :=
  SubsetSF gamma /\
  SF (omega, a) /\
  forall m nu rho,
    (forall p, gamma p -> Satisfies m nu rho (fst p) (snd p)) ->
    Satisfies m nu rho omega a.

Definition ClosureDifferent (k : Library) (omega : State) (a b : Frm) : Prop :=
  ~ ClEq k omega a b.

Theorem non_alpha_collapse_from_closure_difference :
  forall k omega phi psi,
    FiniteLibrary k ->
    SF (omega, phi) ->
    SF (omega, psi) ->
    OrdAlpha (forget_frm phi) (forget_frm psi) ->
    ClosureDifferent k omega phi psi ->
    ~ OwnAlpha phi psi.
Proof.
  intros k omega phi psi Hfin Hsf_phi Hsf_psi _ Hdiff Halpha.
  apply Hdiff.
  now apply cl_alpha_invariant.
Qed.

Definition owner0 : Term := TOwner 0.
Definition owner1 : Term := TOwner 1.
Definition owner2 : Term := TOwner 2.
Definition x0 : Term := TVar 0 0.
Definition x1 : Term := TVar 1 0.
Definition delta0 : Core := vcore 0.

Section ConcreteCollapseShape.

Variable P : R.
Hypothesis P_unary : arR P = 1.

Definition p_of (t : Term) : Frm := FRel P (TCons t TNil).

Definition C1 : Ctx :=
  CtxCons
    (CertLine owner0 (FOwn MWrite owner0 x0) DepInit DepInit
      (KMove owner0 owner1 delta0))
    (CtxCons
      (CertLine owner1 (FOwn MWrite owner1 x0) DepInit DepInit
        (KCopy owner1 owner2 delta0))
      CtxNil).

Definition C2 : Ctx :=
  CtxCons
    (CertLine owner0 (FOwn MWrite owner0 x1) DepInit DepInit
      (KMove owner0 owner1 delta0))
    (CtxCons
      (CertLine owner1 (FOwn MWrite owner1 x1) DepInit DepInit
        (KRead owner2 delta0))
      CtxNil).

Definition Cs : Ctx :=
  CtxCons
    (CertLine owner2 (FOwn MWrite owner2 x0) DepInit DepInit
      (KSubst owner2 delta0 owner2))
    CtxNil.

Definition Phi : Frm := FAll x0 owner0 owner1 C1 (p_of x0).
Definition Psi : Frm := FAll x1 owner0 owner1 C2 (p_of x1).

Definition ExampleLibrary : Library :=
  fun c => c = C1 \/ c = C2 \/ c = Cs.

Lemma finite_example_library :
  FiniteLibrary ExampleLibrary.
Proof.
  unfold FiniteLibrary, ExampleLibrary.
  exists [C1; C2; Cs].
  intros c [Hc | [Hc | Hc]]; subst; simpl; auto.
Qed.

Lemma C1_has_copy :
  HasCopy C1.
Proof.
  simpl. exact I.
Qed.

Theorem concrete_shape_not_own_alpha_if_closures_differ :
  forall omega,
    FiniteLibrary ExampleLibrary ->
    SF (omega, Phi) ->
    SF (omega, Psi) ->
    OrdAlpha (forget_frm Phi) (forget_frm Psi) ->
    ClosureDifferent ExampleLibrary omega Phi Psi ->
    ~ OwnAlpha Phi Psi.
Proof.
  intros omega Hfin Hsf_phi Hsf_psi Hord Hdiff.
  exact (non_alpha_collapse_from_closure_difference
    ExampleLibrary omega Phi Psi Hfin Hsf_phi Hsf_psi Hord Hdiff).
Qed.

End ConcreteCollapseShape.

Definition Section17SubstitutedBody (P : R) : Frm :=
  p_of P owner2.

Lemma section17_substitution_shape :
  forall P,
    SubCoreF (p_of P x0) delta0 owner2 (Section17SubstitutedBody P).
Proof.
  intros P.
  unfold p_of, Section17SubstitutedBody.
  apply SCFRel.
  apply SCTermsCons.
  - apply SCTRoot.
    + unfold CAOKT.
      intros p gamma _ _ Hact.
      unfold ActCore in Hact.
      destruct Hact as [r [d [u [v [Hsub _]]]]].
      destruct r as [| n r]; simpl in Hsub; discriminate.
    + unfold FRoot.
      simpl.
      split; [reflexivity |].
      split.
      * exists x0. simpl. split; [reflexivity | reflexivity].
      * intros q u Hfr Hproper _.
        subst q.
        destruct Hproper as [_ Hneq].
        contradiction.
  - apply SCTermsNil.
Qed.

Definition Section17ConcreteClosureDifference
    (phi psi : Frm) (omega : State) (k : Library) : Prop :=
  exists P omega1 body,
    arR P = 1 /\
    phi = Phi P /\
    psi = Psi P /\
    k = ExampleLibrary /\
    body = Section17SubstitutedBody P /\
    SubCoreF (p_of P x0) delta0 owner2 body /\
    StepCtx C1 omega omega1 /\
    StateHas omega1 owner2 delta0 MWrite /\
    Cl k omega phi (omega1, body) /\
    ~ Cl k omega psi (omega1, body).

Theorem section17_concrete_difference_implies_closure_different :
  forall phi psi omega k,
    Section17ConcreteClosureDifference phi psi omega k ->
    ClosureDifferent k omega phi psi.
Proof.
  unfold Section17ConcreteClosureDifference, ClosureDifferent, ClEq.
  intros phi psi omega k
    [P [omega1 [body
      [_ [_ [_ [_ [_ [_ [_ [_ [Hin Hnotin]]]]]]]]]]]] Heq.
  specialize (Heq (omega1, body)).
  destruct Heq as [Hforward _].
  exact (Hnotin (Hforward Hin)).
Qed.

Fixpoint HasReadAct (c : Ctx) : Prop :=
  match c with
  | CtxNil => False
  | CtxCons (CertLine _ _ _ _ (KRead _ _)) _ => True
  | CtxCons _ rest => HasReadAct rest
  end.

Lemma C2_has_read :
  HasReadAct C2.
Proof.
  simpl. exact I.
Qed.

Definition IsSection17Witness
    (phi psi : Frm) (omega : State) (k : Library) : Prop :=
  exists P : R,
    arR P = 1 /\
    phi = Phi P /\
    psi = Psi P /\
    k = ExampleLibrary /\
    StateHas omega owner0 delta0 MWrite /\
    (forall a delta m,
      StateHas omega a delta m ->
      a = owner0 /\ delta = delta0 /\ m = MWrite).

Definition ClosureDifferenceFromCopyRead
    (phi psi : Frm) (omega : State) (k : Library) : Prop :=
  Section17ConcreteClosureDifference phi psi omega k /\
  IsSection17Witness phi psi omega k /\
  exists omega_copy omega_read,
    StepCtx C1 omega omega_copy /\
    StepCtx C2 omega omega_read /\
    StateHas omega_copy owner2 delta0 MWrite /\
    StateHas omega_read owner2 delta0 MRead /\
    HasCopy C1 /\
    HasReadAct C2.

Definition DeltaO : Prop :=
  exists phi psi omega k,
    IsSection17Witness phi psi omega k /\
    FiniteLibrary k /\
    SF (omega, phi) /\
    SF (omega, psi) /\
    OrdAlpha (forget_frm phi) (forget_frm psi) /\
    ClosureDifferent k omega phi psi /\
    Section17ConcreteClosureDifference phi psi omega k /\
    ClosureDifferenceFromCopyRead phi psi omega k.

Definition DeltaOWithOrdAlphaReplacement : Prop :=
  exists phi psi omega k,
    IsSection17Witness phi psi omega k /\
    FiniteLibrary k /\
    SF (omega, phi) /\
    SF (omega, psi) /\
    OrdAlpha (forget_frm phi) (forget_frm psi) /\
    ClosureDifferentOrdAlpha k omega phi psi.

Theorem ordinary_alpha_replacement_invalidates_delta :
  ~ DeltaOWithOrdAlphaReplacement.
Proof.
  intros [phi [psi [omega [k [_ [Hfin [Hsf_phi [Hsf_psi [Hord Hdiff]]]]]]]]].
  apply Hdiff.
  now apply cl_ord_alpha_invariant.
Qed.

Record OwnershipTransferBindingSystem : Type := {
  sys_Name : Type := Name;
  sys_Obj : Type := Obj;
  sys_Own : Type := Own;
  sys_Term : Type := Term;
  sys_Frm : Type := Frm;
  sys_Ctx : Type := Ctx;
  sys_Core : Type := Core;
  sys_StateFrm : Type := StateFrm;
  sys_SF : StateFrm -> Prop := SF;
  sys_FiniteLibrary : Library -> Prop := FiniteLibrary;
  sys_WellTerm : Term -> Prop := WellTerm;
  sys_WellFrm : Frm -> Prop := WellFrm;
  sys_WellCtxStruct : Ctx -> Prop := WellCtxStruct;
  sys_core : Term -> Core := term_core;
  sys_fshape : Frm -> Core := fshape;
  sys_CtxOK : Ctx -> Prop := CtxOK;
  sys_NameOK : Frm -> Prop := NameOK;
  sys_SubCoreT : Term -> Core -> Term -> Term -> Prop := SubCoreT;
  sys_SubCoreF : Frm -> Core -> Term -> Frm -> Prop := SubCoreF;
  sys_SubCoreC : Ctx -> Core -> Term -> Ctx -> Prop := SubCoreC;
  sys_SubPortF : Frm -> Core -> Frm -> Frm -> Prop := SubPortF;
  sys_SubPortC : Ctx -> Core -> Frm -> Ctx -> Prop := SubPortC;
  sys_Step : Ctx -> State -> State -> Prop := StepCtx;
  sys_Forms : State -> Frm -> Prop := Forms;
  sys_OrdAlpha : OrdFrm -> OrdFrm -> Prop := OrdAlpha;
  sys_BehEq : Ctx -> Ctx -> Core -> Prop := BehEq;
  sys_OwnAlpha : Frm -> Frm -> Prop := OwnAlpha;
  sys_ClMinus : Library -> State -> Frm -> SetOf StateFrm := ClMinus;
  sys_ResMinus : Core -> Library -> State -> Frm -> SetOf StateFrm := ResMinus;
  sys_Cl : Library -> State -> Frm -> SetOf StateFrm := Cl;
  sys_Res : Core -> Library -> State -> Frm -> SetOf StateFrm := Res;
  sys_ClOrdAlpha : Library -> State -> Frm -> SetOf StateFrm := ClOrdAlpha;
  sys_Section17SubstitutionShape :
    forall P,
      SubCoreF (p_of P x0) delta0 owner2 (Section17SubstitutedBody P) :=
    section17_substitution_shape;
  sys_Section17ConcreteClosureDifference :
    Frm -> Frm -> State -> Library -> Prop := Section17ConcreteClosureDifference;
  sys_Section17ConcreteDifferenceImpliesClosureDifferent :
    forall phi psi omega k,
      Section17ConcreteClosureDifference phi psi omega k ->
      ClosureDifferent k omega phi psi :=
    section17_concrete_difference_implies_closure_different;
  sys_OrdAlphaReplacementInvalid :
    ~ DeltaOWithOrdAlphaReplacement := ordinary_alpha_replacement_invalidates_delta;
  sys_Ax : State -> Frm -> Prop := Ax;
  sys_Rule : list StateFrm -> StateFrm -> Prop := RuleO;
  sys_Derives : SetOf StateFrm -> StateFrm -> Prop := Derives;
  sys_Satisfies : forall m, (Obj -> carrier m) -> PortVal -> State -> Frm -> Prop := Satisfies;
  sys_semantic_nontrivial :
    exists m : Model,
    exists nu : Obj -> carrier m,
    exists rho : PortVal,
    exists omega : State,
      Satisfies m nu rho omega reflexive_owner_equality /\
      ~ Satisfies m nu rho omega (FNeg reflexive_owner_equality)
    := ownership_semantics_nontrivial;
  sys_SemEntails : SetOf StateFrm -> State -> Frm -> Prop := SemEntails;
  sys_DeltaO : Prop := DeltaO
}.

End GenericSignature.

End OwnershipTransferBindingLogic.

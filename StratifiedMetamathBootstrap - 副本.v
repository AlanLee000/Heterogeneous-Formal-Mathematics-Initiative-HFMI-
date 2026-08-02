From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.

Import ListNotations.

Unset Automatic Proposition Inductives.

Module StratifiedMetamathematicalBootstrap.

Definition Var : Type := nat.

Definition remove_var (x : Var) (xs : list Var) : list Var :=
  remove Nat.eq_dec x xs.

Fixpoint fresh_from (fuel n : nat) (xs : list Var) : Var :=
  match fuel with
  | O => n
  | S fuel' =>
      if in_dec Nat.eq_dec n xs
      then fresh_from fuel' (S n) xs
      else n
  end.

Definition fresh (xs : list Var) : Var :=
  fresh_from (S (length xs)) 0 xs.

Inductive Term : Type :=
| TVar : Var -> Term
| TQuote : nat -> Var -> Frm -> Term
with Frm : Type :=
| FEq : Term -> Term -> Frm
| FMer : Term -> Term -> Frm
| FSat : nat -> Term -> Term -> Frm
| FDom : nat -> Term -> Frm
| FNeg : Frm -> Frm
| FAnd : Frm -> Frm -> Frm
| FOr : Frm -> Frm -> Frm
| FImp : Frm -> Frm -> Frm
| FAll : Var -> Frm -> Frm
| FEx : Var -> Frm -> Frm.

Definition FIff (a b : Frm) : Frm :=
  FAnd (FImp a b) (FImp b a).

Fixpoint fvT (t : Term) : list Var :=
  match t with
  | TVar x => [x]
  | TQuote _ x a => remove_var x (fvF a)
  end
with fvF (a : Frm) : list Var :=
  match a with
  | FEq s t => fvT s ++ fvT t
  | FMer s t => fvT s ++ fvT t
  | FSat _ s t => fvT s ++ fvT t
  | FDom _ t => fvT t
  | FNeg b => fvF b
  | FAnd b c => fvF b ++ fvF c
  | FOr b c => fvF b ++ fvF c
  | FImp b c => fvF b ++ fvF c
  | FAll x b => remove_var x (fvF b)
  | FEx x b => remove_var x (fvF b)
  end.

Fixpoint bvT (t : Term) : list Var :=
  match t with
  | TVar _ => []
  | TQuote _ x a => x :: bvF a
  end
with bvF (a : Frm) : list Var :=
  match a with
  | FEq s t => bvT s ++ bvT t
  | FMer s t => bvT s ++ bvT t
  | FSat _ s t => bvT s ++ bvT t
  | FDom _ t => bvT t
  | FNeg b => bvF b
  | FAnd b c => bvF b ++ bvF c
  | FOr b c => bvF b ++ bvF c
  | FImp b c => bvF b ++ bvF c
  | FAll x b => x :: bvF b
  | FEx x b => x :: bvF b
  end.

Inductive TermAt : nat -> Term -> Prop :=
| TermAtVar0 :
    forall x, TermAt 0 (TVar x)
| TermAtSucc :
    forall n t, TermAt n t -> TermAt (S n) t
| TermAtQuote :
    forall n x a, FrmAt n a -> TermAt (S n) (TQuote n x a)
with FrmAt : nat -> Frm -> Prop :=
| FrmAtEq :
    forall n s t, TermAt n s -> TermAt n t -> FrmAt n (FEq s t)
| FrmAtMer :
    forall n s t, TermAt n s -> TermAt n t -> FrmAt n (FMer s t)
| FrmAtSat :
    forall n k s t,
      1 <= k ->
      k <= n ->
      TermAt n s ->
      TermAt n t ->
      FrmAt n (FSat k s t)
| FrmAtDom :
    forall n k t,
      k <= n ->
      TermAt n t ->
      FrmAt n (FDom k t)
| FrmAtNeg :
    forall n a, FrmAt n a -> FrmAt n (FNeg a)
| FrmAtAnd :
    forall n a b, FrmAt n a -> FrmAt n b -> FrmAt n (FAnd a b)
| FrmAtOr :
    forall n a b, FrmAt n a -> FrmAt n b -> FrmAt n (FOr a b)
| FrmAtImp :
    forall n a b, FrmAt n a -> FrmAt n b -> FrmAt n (FImp a b)
| FrmAtAll :
    forall n x a, FrmAt n a -> FrmAt n (FAll x a)
| FrmAtEx :
    forall n x a, FrmAt n a -> FrmAt n (FEx x a)
| FrmAtSucc :
    forall n a, FrmAt n a -> FrmAt (S n) a.

Definition TermOmega (t : Term) : Prop :=
  exists n, TermAt n t.

Definition FrmOmega (a : Frm) : Prop :=
  exists n, FrmAt n a.

Inductive AtFrm : Frm -> Prop :=
| AtEq : forall s t, TermOmega s -> TermOmega t -> AtFrm (FEq s t)
| AtMer : forall s t, TermOmega s -> TermOmega t -> AtFrm (FMer s t)
| AtSat :
    forall k s t,
      1 <= k ->
      TermOmega s ->
      TermOmega t ->
      AtFrm (FSat k s t)
| AtDom : forall k t, TermOmega t -> AtFrm (FDom k t).

Definition NonVarTerm (t : Term) : Prop :=
  match t with
  | TVar _ => False
  | TQuote _ _ _ => True
  end.

Fixpoint FreeForT (s : Term) (x : Var) (t : Term) {struct t} : Prop :=
  match t with
  | TVar _ => True
  | TQuote _ y a =>
      ~ In x (fvT t) \/
      (~ In y (fvT s) /\ FreeForF s x a)
  end
with FreeForF (s : Term) (x : Var) (a : Frm) {struct a} : Prop :=
  match a with
  | FEq t u => FreeForT s x t /\ FreeForT s x u
  | FMer t u => FreeForT s x t /\ FreeForT s x u
  | FSat _ t u => FreeForT s x t /\ FreeForT s x u
  | FDom _ t => FreeForT s x t
  | FNeg b => FreeForF s x b
  | FAnd b c => FreeForF s x b /\ FreeForF s x c
  | FOr b c => FreeForF s x b /\ FreeForF s x c
  | FImp b c => FreeForF s x b /\ FreeForF s x c
  | FAll y b =>
      ~ In x (fvF (FAll y b)) \/
      (~ In y (fvT s) /\ FreeForF s x b)
  | FEx y b =>
      ~ In x (fvF (FEx y b)) \/
      (~ In y (fvT s) /\ FreeForF s x b)
  end.

Inductive SubT : Term -> Var -> Term -> Term -> Prop :=
| SubTVarSame :
    forall x s, SubT (TVar x) x s s
| SubTVarDiff :
    forall x y s, y <> x -> SubT (TVar y) x s (TVar y)
| SubTQuoteShadow :
    forall n x a s,
      SubT (TQuote n x a) x s (TQuote n x a)
| SubTQuoteClear :
    forall n x y a s a',
      y <> x ->
      ~ In y (fvT s) ->
      SubF a x s a' ->
      SubT (TQuote n y a) x s (TQuote n y a')
| SubTQuoteCapture :
    forall n x y a s z a1 a2,
      y <> x ->
      In y (fvT s) ->
      z = fresh (fvF a ++ fvT s ++ [x; y]) ->
      SubF a y (TVar z) a1 ->
      SubF a1 x s a2 ->
      SubT (TQuote n y a) x s (TQuote n z a2)
with SubF : Frm -> Var -> Term -> Frm -> Prop :=
| SubFEq :
    forall x s t u t' u',
      SubT t x s t' ->
      SubT u x s u' ->
      SubF (FEq t u) x s (FEq t' u')
| SubFMer :
    forall x s t u t' u',
      SubT t x s t' ->
      SubT u x s u' ->
      SubF (FMer t u) x s (FMer t' u')
| SubFSat :
    forall k x s t u t' u',
      SubT t x s t' ->
      SubT u x s u' ->
      SubF (FSat k t u) x s (FSat k t' u')
| SubFDom :
    forall k x s t t',
      SubT t x s t' ->
      SubF (FDom k t) x s (FDom k t')
| SubFNeg :
    forall x s a a',
      SubF a x s a' ->
      SubF (FNeg a) x s (FNeg a')
| SubFAnd :
    forall x s a b a' b',
      SubF a x s a' ->
      SubF b x s b' ->
      SubF (FAnd a b) x s (FAnd a' b')
| SubFOr :
    forall x s a b a' b',
      SubF a x s a' ->
      SubF b x s b' ->
      SubF (FOr a b) x s (FOr a' b')
| SubFImp :
    forall x s a b a' b',
      SubF a x s a' ->
      SubF b x s b' ->
      SubF (FImp a b) x s (FImp a' b')
| SubFAllShadow :
    forall x a s,
      SubF (FAll x a) x s (FAll x a)
| SubFAllClear :
    forall x y a s a',
      y <> x ->
      ~ In y (fvT s) ->
      SubF a x s a' ->
      SubF (FAll y a) x s (FAll y a')
| SubFAllCapture :
    forall x y a s z a1 a2,
      y <> x ->
      In y (fvT s) ->
      z = fresh (fvF a ++ fvT s ++ [x; y]) ->
      SubF a y (TVar z) a1 ->
      SubF a1 x s a2 ->
      SubF (FAll y a) x s (FAll z a2)
| SubFExShadow :
    forall x a s,
      SubF (FEx x a) x s (FEx x a)
| SubFExClear :
    forall x y a s a',
      y <> x ->
      ~ In y (fvT s) ->
      SubF a x s a' ->
      SubF (FEx y a) x s (FEx y a')
| SubFExCapture :
    forall x y a s z a1 a2,
      y <> x ->
      In y (fvT s) ->
      z = fresh (fvF a ++ fvT s ++ [x; y]) ->
      SubF a y (TVar z) a1 ->
      SubF a1 x s a2 ->
      SubF (FEx y a) x s (FEx z a2).

Definition FreeRenT (t : Term) (x y : Var) (u : Term) : Prop :=
  SubT t x (TVar y) u.

Definition FreeRenF (a : Frm) (x y : Var) (b : Frm) : Prop :=
  SubF a x (TVar y) b.

Definition BoundRenDelta (t : Term) (x y : Var) (u : Term) : Prop :=
  exists n a b,
    t = TQuote n x a /\
    ~ In y (remove_var x (fvF a)) /\
    SubF a x (TVar y) b /\
    u = TQuote n y b.

Definition BoundRenQ (a : Frm) (x y : Var) (b : Frm) : Prop :=
  (exists c d,
    a = FAll x c /\
    ~ In y (remove_var x (fvF c)) /\
    SubF c x (TVar y) d /\
    b = FAll y d) \/
  (exists c d,
    a = FEx x c /\
    ~ In y (remove_var x (fvF c)) /\
    SubF c x (TVar y) d /\
    b = FEx y d).

Inductive AlphaT : Term -> Term -> Prop :=
| AlphaTRefl :
    forall t, AlphaT t t
| AlphaTSym :
    forall s t, AlphaT s t -> AlphaT t s
| AlphaTTrans :
    forall r s t, AlphaT r s -> AlphaT s t -> AlphaT r t
| AlphaTVar :
    forall x, AlphaT (TVar x) (TVar x)
| AlphaTQuoteCompat :
    forall n x a b,
      AlphaF a b ->
      AlphaT (TQuote n x a) (TQuote n x b)
| AlphaTQuoteRename :
    forall n x y a b,
      FrmAt n a ->
      ~ In y (remove_var x (fvF a)) ->
      SubF a x (TVar y) b ->
      AlphaT (TQuote n x a) (TQuote n y b)
with AlphaF : Frm -> Frm -> Prop :=
| AlphaFRefl :
    forall a, AlphaF a a
| AlphaFSym :
    forall a b, AlphaF a b -> AlphaF b a
| AlphaFTrans :
    forall a b c, AlphaF a b -> AlphaF b c -> AlphaF a c
| AlphaFEqCompat :
    forall s0 s1 t0 t1,
      AlphaT s0 s1 ->
      AlphaT t0 t1 ->
      AlphaF (FEq s0 t0) (FEq s1 t1)
| AlphaFMerCompat :
    forall s0 s1 t0 t1,
      AlphaT s0 s1 ->
      AlphaT t0 t1 ->
      AlphaF (FMer s0 t0) (FMer s1 t1)
| AlphaFSatCompat :
    forall k s0 s1 t0 t1,
      AlphaT s0 s1 ->
      AlphaT t0 t1 ->
      AlphaF (FSat k s0 t0) (FSat k s1 t1)
| AlphaFDomCompat :
    forall k t0 t1,
      AlphaT t0 t1 ->
      AlphaF (FDom k t0) (FDom k t1)
| AlphaFNegCompat :
    forall a b, AlphaF a b -> AlphaF (FNeg a) (FNeg b)
| AlphaFAndCompat :
    forall a0 a1 b0 b1,
      AlphaF a0 a1 ->
      AlphaF b0 b1 ->
      AlphaF (FAnd a0 b0) (FAnd a1 b1)
| AlphaFOrCompat :
    forall a0 a1 b0 b1,
      AlphaF a0 a1 ->
      AlphaF b0 b1 ->
      AlphaF (FOr a0 b0) (FOr a1 b1)
| AlphaFImpCompat :
    forall a0 a1 b0 b1,
      AlphaF a0 a1 ->
      AlphaF b0 b1 ->
      AlphaF (FImp a0 b0) (FImp a1 b1)
| AlphaFAllCompat :
    forall x a b,
      AlphaF a b ->
      AlphaF (FAll x a) (FAll x b)
| AlphaFExCompat :
    forall x a b,
      AlphaF a b ->
      AlphaF (FEx x a) (FEx x b)
| AlphaFAllRename :
    forall x y a b,
      FrmOmega a ->
      ~ In y (remove_var x (fvF a)) ->
      SubF a x (TVar y) b ->
      AlphaF (FAll x a) (FAll y b)
| AlphaFExRename :
    forall x y a b,
      FrmOmega a ->
      ~ In y (remove_var x (fvF a)) ->
      SubF a x (TVar y) b ->
      AlphaF (FEx x a) (FEx y b).

Inductive Ax : Frm -> Prop :=
| AxH1 :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp a (FImp b a))
| AxH2 :
    forall a b c,
      FrmOmega a ->
      FrmOmega b ->
      FrmOmega c ->
      Ax (FImp (FImp a (FImp b c)) (FImp (FImp a b) (FImp a c)))
| AxH3Left :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp (FAnd a b) a)
| AxH3Right :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp (FAnd a b) b)
| AxH4 :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp a (FImp b (FAnd a b)))
| AxH5Left :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp a (FOr a b))
| AxH5Right :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp b (FOr a b))
| AxH6 :
    forall a b c,
      FrmOmega a ->
      FrmOmega b ->
      FrmOmega c ->
      Ax (FImp (FImp a c) (FImp (FImp b c) (FImp (FOr a b) c)))
| AxH7 :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp (FImp a b) (FImp (FImp a (FNeg b)) (FNeg a)))
| AxH8 :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      Ax (FImp (FNeg a) (FImp a b))
| AxH9 :
    forall x a t a_sub,
      FrmOmega a ->
      TermOmega t ->
      FreeForF t x a ->
      SubF a x t a_sub ->
      Ax (FImp (FAll x a) a_sub)
| AxH10 :
    forall x a b,
      FrmOmega a ->
      FrmOmega b ->
      ~ In x (fvF a) ->
      Ax (FImp (FAll x (FImp a b)) (FImp a (FAll x b)))
| AxH11 :
    forall x a t a_sub,
      FrmOmega a ->
      TermOmega t ->
      FreeForF t x a ->
      SubF a x t a_sub ->
      Ax (FImp a_sub (FEx x a))
| AxH12 :
    forall x a b,
      FrmOmega a ->
      FrmOmega b ->
      ~ In x (fvF b) ->
      Ax (FImp (FAll x (FImp a b)) (FImp (FEx x a) b))
| AxI1 :
    forall x,
      Ax (FEq (TVar x) (TVar x))
| AxI2 :
    forall x y a ay,
      AtFrm a ->
      FreeForF (TVar y) x a ->
      SubF a x (TVar y) ay ->
      Ax (FImp (FEq (TVar x) (TVar y)) (FImp a ay))
| AxI3 :
    forall x y s sy,
      TermOmega s ->
      NonVarTerm s ->
      FreeForT (TVar y) x s ->
      SubT s x (TVar y) sy ->
      Ax (FImp (FEq (TVar x) (TVar y)) (FEq s sy))
| AxM1 :
    forall x,
      Ax (FImp (FDom 0 (TVar x)) (FMer (TVar x) (TVar x)))
| AxM2 :
    forall x y,
      Ax
        (FImp
          (FAnd
            (FAnd (FDom 0 (TVar x)) (FDom 0 (TVar y)))
            (FAnd (FMer (TVar x) (TVar y)) (FMer (TVar y) (TVar x))))
          (FEq (TVar x) (TVar y)))
| AxM3 :
    forall x y z,
      Ax
        (FImp
          (FAnd
            (FAnd (FDom 0 (TVar x)) (FDom 0 (TVar y)))
            (FAnd (FDom 0 (TVar z))
              (FAnd (FMer (TVar x) (TVar y)) (FMer (TVar y) (TVar z)))))
          (FMer (TVar x) (TVar z)))
| AxC1 :
    forall n x,
      Ax (FImp (FDom n (TVar x)) (FDom (S n) (TVar x)))
| AxC2 :
    forall n x a,
      FrmAt n a ->
      Ax
        (FAnd
          (FDom (S n) (TQuote n x a))
          (FNeg (FDom n (TQuote n x a))))
| AxC3 :
    forall n a b u v x avx bux,
      FrmAt n a ->
      FrmAt n b ->
      FreeForF (TVar x) v a ->
      FreeForF (TVar x) u b ->
      ~ In x (fvT (TQuote n v a) ++ fvT (TQuote n u b)) ->
      SubF a v (TVar x) avx ->
      SubF b u (TVar x) bux ->
      Ax
        (FIff
          (FEq (TQuote n v a) (TQuote n u b))
          (FAll x (FImp (FDom n (TVar x)) (FIff avx bux))))
| AxC4 :
    forall n a v x avx,
      FrmAt n a ->
      FreeForF (TVar x) v a ->
      SubF a v (TVar x) avx ->
      Ax
        (FImp
          (FDom n (TVar x))
          (FIff (FSat (S n) (TVar x) (TQuote n v a)) (FNeg avx)))
| AxC5 :
    forall n x y,
      Ax
        (FImp
          (FSat (S n) (TVar x) (TVar y))
          (FAnd
            (FDom n (TVar x))
            (FAnd (FDom (S n) (TVar y)) (FNeg (FDom n (TVar y)))))).

Inductive RuleBare : list Frm -> Frm -> Prop :=
| RuleImp :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      RuleBare [a; FImp a b] b
| RuleAll :
    forall x a,
      FrmOmega a ->
      RuleBare [a] (FAll x a)
| RuleAlpha :
    forall a b,
      FrmOmega a ->
      FrmOmega b ->
      AlphaF a b ->
      RuleBare [a] b.

Definition FVGamma (gamma : Frm -> Prop) (x : Var) : Prop :=
  exists a, gamma a /\ In x (fvF a).

Inductive LineOK (gamma : Frm -> Prop) (seen : list Frm) : Frm -> Prop :=
| LineHyp :
    forall a,
      FrmOmega a ->
      gamma a ->
      LineOK gamma seen a
| LineAx :
    forall a,
      FrmOmega a ->
      Ax a ->
      LineOK gamma seen a
| LineMP :
    forall a b,
      FrmOmega b ->
      In a seen ->
      In (FImp a b) seen ->
      LineOK gamma seen b
| LineAll :
    forall x a,
      FrmOmega (FAll x a) ->
      In a seen ->
      ~ FVGamma gamma x ->
      LineOK gamma seen (FAll x a)
| LineAlpha :
    forall a b,
      FrmOmega b ->
      In a seen ->
      AlphaF a b ->
      LineOK gamma seen b.

Fixpoint LinesOK
    (gamma : Frm -> Prop) (seen pi : list Frm) {struct pi} : Prop :=
  match pi with
  | [] => True
  | a :: rest => LineOK gamma seen a /\ LinesOK gamma (seen ++ [a]) rest
  end.

Definition ProofFrom (gamma : Frm -> Prop) (pi : list Frm) : Prop :=
  pi <> [] /\ LinesOK gamma [] pi.

Fixpoint last_formula (pi : list Frm) : option Frm :=
  match pi with
  | [] => None
  | [a] => Some a
  | _ :: rest => last_formula rest
  end.

Definition Derivable (gamma : Frm -> Prop) (a : Frm) : Prop :=
  exists pi, ProofFrom gamma pi /\ last_formula pi = Some a.

Definition TheoremF (a : Frm) : Prop :=
  Derivable (fun _ => False) a.

Definition ThmSet : Frm -> Prop := TheoremF.

Record StratifiedMetamathSystem : Type := {
  sys_Var : Type;
  sys_Term : Type;
  sys_Frm : Type;
  sys_TermAt : nat -> Term -> Prop;
  sys_FrmAt : nat -> Frm -> Prop;
  sys_TermOmega : Term -> Prop;
  sys_FrmOmega : Frm -> Prop;
  sys_fvT : Term -> list Var;
  sys_fvF : Frm -> list Var;
  sys_bvT : Term -> list Var;
  sys_bvF : Frm -> list Var;
  sys_FreeForT : Term -> Var -> Term -> Prop;
  sys_FreeForF : Term -> Var -> Frm -> Prop;
  sys_SubT : Term -> Var -> Term -> Term -> Prop;
  sys_SubF : Frm -> Var -> Term -> Frm -> Prop;
  sys_AlphaT : Term -> Term -> Prop;
  sys_AlphaF : Frm -> Frm -> Prop;
  sys_Ax : Frm -> Prop;
  sys_RuleBare : list Frm -> Frm -> Prop;
  sys_ProofFrom : (Frm -> Prop) -> list Frm -> Prop;
  sys_Derivable : (Frm -> Prop) -> Frm -> Prop;
  sys_TheoremF : Frm -> Prop
}.

Definition T_omega_star : StratifiedMetamathSystem := {|
  sys_Var := Var;
  sys_Term := Term;
  sys_Frm := Frm;
  sys_TermAt := TermAt;
  sys_FrmAt := FrmAt;
  sys_TermOmega := TermOmega;
  sys_FrmOmega := FrmOmega;
  sys_fvT := fvT;
  sys_fvF := fvF;
  sys_bvT := bvT;
  sys_bvF := bvF;
  sys_FreeForT := FreeForT;
  sys_FreeForF := FreeForF;
  sys_SubT := SubT;
  sys_SubF := SubF;
  sys_AlphaT := AlphaT;
  sys_AlphaF := AlphaF;
  sys_Ax := Ax;
  sys_RuleBare := RuleBare;
  sys_ProofFrom := ProofFrom;
  sys_Derivable := Derivable;
  sys_TheoremF := TheoremF
|}.

End StratifiedMetamathematicalBootstrap.

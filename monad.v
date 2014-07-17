(* (c) Copyright ? *)

(*****************************************************************************
  Monads and monad transformations mimicking Haskell's.

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect.

Generalizable All Variables.

Class Monad m := {
  ret : forall a, a -> m a;
  bind : forall a, m a -> forall b, (a -> m b) -> m b
}.

Class Monoid m := {
  mempty : m;
  mappend : m -> m -> m
}.

Class MonadWriter w m `{Monoid w, Monad m} := {
  tell : w -> m unit
}.

Arguments MonadWriter _ _ {_ _}.

Record Writer w a := MkWriter{
  runWriter : a * w
}.                                  

Instance Writer_Monad `(Monoid w) : Monad (Writer w) := {
  ret a x := MkWriter (x, mempty);
  bind a ma b f := 
    let: MkWriter (x, log) := ma in
    let: MkWriter (y, log') := f x in
    MkWriter (y, mappend log log')
}.

Definition tellMT `{Monoid w} log : Writer w unit := MkWriter (tt, log).

Instance Writer_MonadWriter `{Monoid w} : MonadWriter w _ := {
  tell := tellMT
}.

Record ErrorT e m a := MkErrorT {
  runErrorT : m (e + a)%type
}.

Notation "x <- a ;; b" := (bind a (fun x => b)) (at level 90, right associativity).
Notation "a ;;; b" := (bind a (fun _ => b)) (at level 90, right associativity).

Definition bindMT `{Monad m} {e} a (x : ErrorT e m a) b (f : a -> ErrorT e m b) := MkErrorT (
  unwrapped <- runErrorT x;;
  match unwrapped with
    | inl err => ret (inl err)
    | inr y => runErrorT (f y)
  end).

Definition retMT `{Monad m} {e} a v : ErrorT e m a := MkErrorT (ret (inr v)).

Instance ErrorT_Monad `{Monad m} e : Monad (ErrorT e m) := {
  ret := retMT;
  bind := bindMT
}.

Class MonadTrans t := {
  lift : forall `{Monad m} {a}, m a -> t m a
}.

Definition liftM `{m_Monad : Monad m} a b (f : a -> b) (ma : m a) : m b :=
  x <- ma;;
  ret (f x).

Instance ErrorT_MonadTrans e : MonadTrans (ErrorT e) := {
  lift := fun _ _ _ ma => MkErrorT (liftM inr ma)
}.

Instance ErrorT_MonadWriter `{Monoid w, Monad m, MonadWriter w m} e : MonadWriter w (ErrorT e m) := {
  tell log := lift (tell log)
}.

Class MonadError e `{Monad m} := {
  throwError : forall {a}, e -> m a;
  catchError : forall {a}, m a -> (e -> m a) -> m a
}.

Arguments MonadError _ _ {_}.

Instance ErrorT_MonadError `{Monad m} e : MonadError e (ErrorT e m) := {
  throwError a l := MkErrorT (ret (inl l));
  catchError a ma h := MkErrorT ( 
    x <- runErrorT ma;;
    match x with
      | inl l => runErrorT (h l)
      | inr r => ret (inr r)
    end)
}.

Instance list_Monoid a : Monoid (list a) := {
  mempty := nil;
  mappend := @app _
}.

Instance sum_Monad e : Monad (sum e) := {
  ret a v := inr v;
  bind a am b f := 
    match am with
      | inl l => inl l
      | inr r => f r
    end
}.

Instance sum_MonadError e : MonadError e (sum e) := {
  throwError a := inl;
  catchError a am h := 
    match am with
      | inl l => h l
      | inr r => inr r
    end
}.

Record WriterT w m a := MkWriterT {
  runWriterT : m (a * w)%type
}.

Instance WriterT_Monad `{Monoid w, Monad m} : Monad (WriterT w m) := {
  ret a x := MkWriterT (ret (x, mempty));
  bind a m b k := MkWriterT (
    t <- runWriterT m;;
    let: (a, w) := t in
    t <- runWriterT (k a);;
    let: (b, w') := t in
    ret (b, mappend w w')
  )
}.

Instance WriterT_MonadTrans `{Monoid w} : MonadTrans (WriterT w) := {
  lift := fun _ _ _ m => MkWriterT (
    a <- m;;
    ret (a, mempty)
  )
}.

Instance WriterT_MonadWrite `{Monoid w, Monad m} : MonadWriter w (WriterT w m) := {
  tell w := MkWriterT (ret (tt, w))
}.

Require Import ssrfun.

Instance WriterT_MonadError e `{Monoid w, Monad m, MonadError e m} : MonadError e (WriterT w m) := {
  throwError a := lift \o throwError;
  catchError a m h := MkWriterT (catchError (runWriterT m) (fun e => runWriterT (h e)))
}.

Require Import String.

Class Error a := {
  strMsg : string -> a
}.
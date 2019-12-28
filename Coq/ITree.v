Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Open Scope string_scope.
Set Implicit Arguments.

(* A simple variant of interaction trees.
   Should form a monad and can be seen as a computation. *)
Inductive ITree(A: Type) :=
| IOut(msg: string)(void_cont: unit -> ITree A)
| IIn(str_cont: string -> ITree A)
| IRet(a: A).

Fixpoint IBind{A B: Type}(m: ITree A)(f: A -> ITree B): ITree B :=
  match m with
  | IOut msg void_cont => IOut msg (fun tt => IBind (void_cont tt) f)
  | IIn str_cont => IIn (fun a => IBind (str_cont a) f)
  | IRet a => f a
  end.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f = f a;
  right_identity: forall {A} (m: M A),
    Bind m Return = m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g = Bind m (fun x => Bind (f x) g)
}.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

(* We can define a function which works for all monads *)
Definition when{M: Type -> Type}{MM: Monad M}(a: bool)(b: M unit): M unit :=
  if a then b else Return tt.

(* Monad laws for ITree *)
Definition IBind_IRet_l {A B} a b : @IBind A B (IRet a) b = b a := eq_refl.
Lemma IBind_assoc {A B C} (a : ITree A) (b : A -> ITree B) (c : B -> ITree C) :
  IBind (IBind a b) c = IBind a (fun x => IBind (b x) c).
Proof.
  revert c; revert C; revert b; revert B; induction a;
    cbn [IBind]; eauto using f_equal, functional_extensionality.
Qed.
Lemma IBind_IRet_r {A} (a : ITree A) : IBind a (@IRet A) = a.
Proof. induction a; cbn [IBind]; eauto using f_equal, functional_extensionality. Qed.
Instance Monad_ITree: Monad ITree.
Proof. esplit; eauto using IBind_IRet_l, IBind_assoc, IBind_IRet_r. Defined.

Definition Read: ITree string := IIn (@IRet string).
Definition Write(msg: string): ITree unit := IOut msg (@IRet unit).

Definition Greeter: ITree unit :=
  Write "Please enter your name: ";;
  name <- Read;
  Write ("Hello, " ++ name).

(* given a list of inputs known a priori,
   interprets the ITree into a list of outputs and an answer *)
Fixpoint interp_feed{A: Type}(t: ITree A)(input: list string): option (list string * A) :=
  match t with
  | IOut msg void_cont => match interp_feed (void_cont tt) input with
                          | Some (outputs, answer) => Some (msg :: outputs, answer)
                          | None => None
                          end
  | IIn str_cont => match input with
                    | inp :: rest => interp_feed (str_cont inp) rest
                    | nil => None (* error: not enough input was provided *)
                    end
  | IRet a => Some (nil, a)
  end.

Eval vm_compute in (interp_feed Greeter ["Daphne"]).
(*
     = Some (["Please enter your name: "; "Hello, Daphne"], tt)
     : option (list string * unit)
*)

Inductive Event :=
| EIn(inp: string)
| EOut(outp: string).

Definition Trace := list Event.

(* Interprets an ITree into the strongest post condition on the trace & answer.
   Note: we do not have to provide a list of inputs here, and we can capture
   all possible non-deterministic executions. *)
Fixpoint interp_prop{A: Type}(m: ITree A): Trace -> A -> Prop :=
  match m with
  | IOut msg void_cont =>
    fun t a => exists tail, t = EOut msg :: tail /\ interp_prop (void_cont tt) tail a
  | IIn str_cont =>
    fun t a => exists head tail, t = EIn head :: tail /\ interp_prop (str_cont head) tail a
  | IRet a => fun t a' => t = nil /\ a' = a
  end.

Eval cbv -[String.append] in (interp_prop Greeter).
(*
     = fun (t : list Event) (a : unit) =>
       exists tail : list Event,
         t = EOut "Please enter your name: " :: tail /\
         (exists (head : string) (tail0 : list Event),
            tail = EIn head :: tail0 /\
            (exists tail1 : list Event,
               tail0 = EOut ("Hello, " ++ head) :: tail1 /\ tail1 = [] /\ a = tt))
     : Trace -> unit -> Prop
*)

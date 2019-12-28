(* The monad usage of https://github.com/mit-plv/riscv-coq, condensed into one stand-alone Coq file *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

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

(* We can define a function which works for all monads *)
Definition when{M: Type -> Type}{MM: Monad M}(a: bool)(b: M unit): M unit :=
  if a then b else Return tt.

Parameter wXLEN: Type. (* 32-bit or 64-bit word, depending on architecture *)
Parameter add: wXLEN -> wXLEN -> wXLEN.
Parameter w8: Type.
Parameter w16: Type.
Parameter w32: Type.
Parameter w64: Type.

Inductive Register := x0 | x1 | x2 | x3. (* up to x31 in actual RISC-V *)

(* We can define a typeclass which puts constraints on a monad:
   It requires that the monad provides the following methods: *)
Class RiscvProgram{M}`{Monad M} := mkRiscvProgram {
  getRegister: Register -> M wXLEN;
  setRegister: Register -> wXLEN -> M unit;

  loadByte   : wXLEN -> M w8;
  loadHalf   : wXLEN -> M w16;
  loadWord   : wXLEN -> M w32;
  loadDouble : wXLEN -> M w64;

  storeByte   : wXLEN -> w8 -> M unit;
  storeHalf   : wXLEN -> w16 -> M unit;
  storeWord   : wXLEN -> w32 -> M unit;
  storeDouble : wXLEN -> w64 -> M unit;

  getPC: M wXLEN;
  setPC: wXLEN -> M unit;
}.


Ltac prove_monad_law :=
  repeat match goal with
         | |- _ => intro
         | |- _ => apply functional_extensionality
         | |- _ => apply propositional_extensionality; split; intros
         | H: exists x, _ |- _ => destruct H
         | H: _ /\ _ |- _ => destruct H
         | p: _ * _ |- _ => destruct p
         | |- context [ let (_, _) := ?p in _ ] => let E := fresh "E" in destruct p eqn: E
         | H: Some _ = Some _ |- _ => inversion H; clear H; subst
         | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
         | |- _ => discriminate
         | |- _ => progress (subst; simpl in *)
         | |- _ => solve [eauto 10]
         | H: _ \/ _ |- _ => destruct H
         | o: option _ |- _ => destruct o
         end.

Instance option_Monad: Monad option. refine ({|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
          | Some x => f x
          | None => None
          end;
  Return := fun {A: Type} (a: A) => Some a
|}).
all: prove_monad_law.
Defined.


Definition NonDet(A: Type): Type := A -> Prop.

Instance NonDet_Monad: Monad NonDet. refine ({|
  Bind{A B}(m: NonDet A)(f: A -> NonDet B) :=
    fun (b: B) => exists a, m a /\ f a b;
  Return{A} := eq;
|}).
all: prove_monad_law.
Defined.


Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S). refine ({|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
            fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (a, s)
|}).
all: prove_monad_law.
Defined.

Module State.
  Definition get{S: Type}: State S S := fun (s: S) => (s, s).
  Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
  Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).
End State.

(* We can think of it as "S -> ((A * S) -> Prop)", i.e. a function returning
   a unique set of all possible outcomes. *)
Definition StateND(S A: Type) := S -> (A * S) -> Prop.

Instance StateND_Monad(S: Type): Monad (StateND S). refine ({|
  Bind{A B}(m: StateND S A)(f : A -> StateND S B) :=
    fun (s1 : S) bs3 => exists a s2, m s1 (a, s2) /\ f a s2 bs3;
  Return{A}(a : A) :=
    fun (s : S) '(a', s') => a' = a /\ s' = s;
|}).
all: prove_monad_law.
Defined.

Module StateND.
  Definition get{S: Type}: StateND S S :=
    fun (s: S) (ss: (S * S)) => ss = (s, s).
  Definition put{S: Type}(new_s: S): StateND S unit :=
    fun (s: S) (us: (unit * S)) => us = (tt, new_s).
  Definition unspecified_behavior{S A: Type}: StateND S A :=
    fun (s: S) (a_s: (A * S)) => True. (* everything's possible (including state changes) *)
  Definition arbitrary{S: Type}(A: Type): StateND S A :=
    fun (s: S) (a_s: (A * S)) => exists a, a_s = (a, s). (* any A is possible, but s remains the same *)
  Definition arbitrary_if_None{S A: Type}(o: option A): StateND S A :=
    match o with
    | Some a => Return a
    | None => arbitrary A
    end.
End StateND.

Inductive InstructionI : Type
  := Lb (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Lh (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Lw (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Lbu (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Lhu (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Fence (pred : Z) (succ : Z)
  |  Fence_i : InstructionI
  |  Addi (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Slli (rd : Register) (rs1 : Register) (shamt6 : Z) : InstructionI
  |  Slti (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Sltiu (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Xori (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Ori (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Andi (rd : Register) (rs1 : Register) (imm12 : Z)
  |  Srli (rd : Register) (rs1 : Register) (shamt6 : Z) : InstructionI
  |  Srai (rd : Register) (rs1 : Register) (shamt6 : Z) : InstructionI
  |  Auipc (rd : Register) (oimm20 : Z) : InstructionI
  |  Sb (rs1 : Register) (rs2 : Register) (simm12 : Z)
  |  Sh (rs1 : Register) (rs2 : Register) (simm12 : Z)
  |  Sw (rs1 : Register) (rs2 : Register) (simm12 : Z)
  |  Add (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Sub (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Sll (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Slt (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Sltu (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Xor (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Srl (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Sra (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Or (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  And (rd : Register) (rs1 : Register) (rs2 : Register) : InstructionI
  |  Lui (rd : Register) (imm20 : Z) : InstructionI
  |  Beq (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Bne (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Blt (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Bge (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Bltu (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Bgeu (rs1 : Register) (rs2 : Register) (sbimm12 : Z)
  |  Jalr (rd : Register) (rs1 : Register) (oimm12 : Z)
  |  Jal (rd : Register) (jimm20 : Z) : InstructionI
  |  InvalidI : InstructionI.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Definition SKIP{T: Type}: T. Admitted.

Definition executeI{M}`{RiscvProgram M}(inst: InstructionI): M unit :=
  match inst with
  | Add rd rs1 rs2 =>
      x <- getRegister rs1; y <- getRegister rs2; setRegister rd (add x y)
  | _ => SKIP
  end.


(* register file with default values *)
Inductive Regfile :=
  mkRegfile: wXLEN -> wXLEN -> wXLEN -> wXLEN -> Regfile.

(* potentially uninitialized register file *)
Inductive URegfile :=
  mkURegfile: option wXLEN -> option wXLEN -> option wXLEN -> option wXLEN -> URegfile.

Definition DetRiscvMachineState := Regfile. (* more state is needed in reality *)

Instance DetMachine: @RiscvProgram (State DetRiscvMachineState) _.
  refine ({|
    getRegister r :=
      m <- State.get;
      let 'mkRegfile r0 r1 r2 r3 := m in
      Return match r with
             | x0 => r0
             | x1 => r1
             | x2 => r2
             | x3 => r3
             end;
    setRegister r v :=
      m <- State.get;
      let 'mkRegfile r0 r1 r2 r3 := m in
      State.put (match r with
                 | x0 => mkRegfile v  r1 r2 r3
                 | x1 => mkRegfile r0 v  r2 r3
                 | x2 => mkRegfile r0 r1 v  r3
                 | x3 => mkRegfile r0 r1 r2 v
                 end);
  |}).
  all: exact SKIP.
Defined.

Eval vm_compute in (fun v0 v1 v2 v3: wXLEN =>
  (@executeI _ _ DetMachine (Add x1 x2 x3) (mkRegfile v0 v1 v2 v3))).
(* prints

   fun v0 _ v2 v3 : wXLEN => (tt, mkRegfile v0 (add v2 v3) v2 v3)

   and we see that this computation has one deterministic result state *)

Definition NondetRiscvMachineState := URegfile. (* more state is needed in reality *)

Instance NondetMachine: @RiscvProgram (StateND NondetRiscvMachineState) _.
  refine ({|
    getRegister r :=
      m <- StateND.get;
      let 'mkURegfile r0 r1 r2 r3 := m in
      match r with
             | x0 => StateND.arbitrary_if_None r0
             | x1 => StateND.arbitrary_if_None r1
             | x2 => StateND.arbitrary_if_None r2
             | x3 => StateND.arbitrary_if_None r3
             end;
    setRegister r v :=
      m <- StateND.get;
      let 'mkURegfile r0 r1 r2 r3 := m in
      StateND.put (match r with
                   | x0 => mkURegfile (Some v)  r1 r2 r3
                   | x1 => mkURegfile r0 (Some v)  r2 r3
                   | x2 => mkURegfile r0 r1 (Some v)  r3
                   | x3 => mkURegfile r0 r1 r2 (Some v)
                   end);
  |}).
  all: exact SKIP.
Defined.

Eval vm_compute in (fun v3: wXLEN =>
  (@executeI _ _ NondetMachine (Add x1 x2 x3) (mkURegfile None None None (Some v3)))).
(* prints a somewhat cumbersome proposition telling all constraints we know on the
   resulting machine *)

(* Free monad *)
Module free.
  Section WithInterface.
    Context {action : Type} {result : action -> Type}.
    Inductive free {T : Type} : Type :=
    | act (a : action) (_ : result a -> free)
    | ret (x : T).
    Arguments free : clear implicits.

    Fixpoint bind {A B} (mx : free A) (fy : A -> free B) : free B :=
      match mx with
      | act a k => act a (fun x => bind (k x) fy)
      | ret x => fy x
      end.

    (** Monad laws *)
    Definition bind_ret_l {A B} a b : @bind A B (ret a) b = b a := eq_refl.
    Lemma bind_assoc {A B C} (a : free A) (b : A -> free B) (c : B -> free C) :
      bind (bind a b) c = bind a (fun x => bind (b x) c).
    Proof. revert c; revert C; revert b; revert B; induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Lemma bind_ret_r {A} (a : free A) : bind a ret = a.
    Proof. induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Global Instance Monad_free : Monad free.
    Proof. esplit; eauto using bind_ret_l, bind_assoc, bind_ret_r. Defined.

    Section WithState.
      Context {state}
      (interp_action : forall a : action, state -> (result a -> state -> Prop) -> Prop).
      Section WithOutput.
        Context {output} (post : output -> state -> Prop).
        Definition interp_body interp (a : free output) (s : state) : Prop :=
          match a with
          | ret x => post x s
          | act a k => interp_action a s (fun r => interp (k r))
          end.
        Fixpoint interp_fix a := interp_body interp_fix a.
      End WithOutput.

      Definition interp {output} a s post := @interp_fix output post a s.

      Lemma interp_ret {T} (x : T) m P : interp (ret x) m P = P x m.
      Proof. exact eq_refl. Qed.
      Lemma interp_act {T} a (k : _ -> free T) s post
        : interp (act a k) s post
        = interp_action a s (fun r s => interp (k r) s post).
      Proof. exact eq_refl. Qed.

      Context (interp_action_weaken_post :
        forall a (post1 post2:_->_->Prop), (forall r s, post1 r s -> post2 r s) -> forall s, interp_action a s post1 -> interp_action a s post2).

      Lemma interp_weaken_post {T} (p : free T) s
        (post1 post2:_->_->Prop) (Hpost : forall r s, post1 r s -> post2 r s)
        (Hinterp : interp p s post1) : interp p s post2.
      Proof. revert dependent s; induction p; cbn; firstorder eauto. Qed.

      Lemma interp_bind {A B} s post (a : free A) (b : A -> free B) :
        interp (bind a b) s post <-> interp a s (fun x s => interp (b x) s post).
      Proof.
        revert post; revert b; revert B; revert s; induction a.
        2: { intros. cbn. reflexivity. }
        split; eapply interp_action_weaken_post; intros; eapply H; eauto.
      Qed.

      Lemma interp_bind_ex_mid {A B} m0 post (a : free A) (b : A -> free B) :
        interp (bind a b) m0 post <->
        (exists mid, interp a m0 mid /\ forall x m1, mid x m1 -> interp (b x) m1 post).
      Proof.
        rewrite interp_bind.
        split; [intros ? | intros (?&?&?)].
        { exists (fun x m1 => interp (b x) m1 post); split; eauto. }
        { eauto using interp_weaken_post. }
      Qed.
    End WithState.

  End WithInterface.
  Global Arguments free : clear implicits.
End free. Notation free := free.free.

Section Riscv.
  Import free.

  Local Notation wxlen := wXLEN.
  Variant action :=
  | A_getRegister (_ : Register)
  | A_setRegister (_ : Register) (_ : wxlen)
  | A_loadByte (_ : wxlen)
  | A_loadHalf (_ : wxlen)
  | A_loadWord (_ : wxlen)
  | A_loadDouble (_ : wxlen)
  | A_storeByte (_ : wxlen) (_ : w8)
  | A_storeHalf (_ : wxlen) (_ : w16)
  | A_storeWord (_ : wxlen) (_ : w32)
  | A_storeDouble (_ : wxlen) (_ : w64)
  | A_getPC
  | A_setPC (_ : wxlen)
  | A_step
  .

  Definition result (action : action) : Type :=
    match action with
    | A_getRegister _ => wxlen
    | A_setRegister _ _ => unit
    | A_loadByte _ => w8
    | A_getPC => wxlen
    | A_loadHalf _ => w16
    | A_loadWord _ => w32
    | A_loadDouble _ => w64
    | A_storeByte _ _ | A_storeHalf _ _ | A_storeWord _ _ | A_storeDouble _ _ => unit
    | A_setPC _ | A_step => unit
    end.

  Local Notation M := (free action result).

  Instance IsRiscvMachine: @RiscvProgram M _ := {|
    getRegister a := act (A_getRegister a) ret;
    setRegister a b := act (A_setRegister a b) ret;
    loadByte b := act (A_loadByte b) ret;
    loadHalf b := act (A_loadHalf b) ret;
    loadWord b := act (A_loadWord b) ret;
    loadDouble b := act (A_loadDouble b) ret;
    storeByte b c := act (A_storeByte b c) ret;
    storeHalf b c := act (A_storeHalf b c) ret;
    storeWord b c := act (A_storeWord b c) ret;
    storeDouble b c := act (A_storeDouble b c) ret;
    getPC := act A_getPC ret;
    setPC a := act (A_setPC a) ret;
  |}.

(* Question: why do we abstract over the monad instead of just hard-coding the free monad, and provide different interps for the free monad?
A: probably for no good reason *)

(*
  Definition interp_action_ND (a : action) (mach : URegfile) : (result a -> URegfile -> Prop) -> Prop :=
    match a with
    | A_getRegister reg => fun post =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach.(getRegs) reg with
               | Some x => x
               | None => word.of_Z 0 end in
        post v mach
    | setRegister reg v => fun post =>
      let regs := if Z.eq_dec reg Register0
                  then mach.(getRegs)
                  else map.put mach.(getRegs) reg v in
      post tt (withRegs regs mach)
    | getPC => fun post => post mach.(getPc) mach
    | setPC newPC => fun post => post tt (withNextPc newPC mach)
    | step => fun post => post tt (withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach))
    | loadByte ctxid a => fun post => load 1 ctxid a mach post
    | loadHalf ctxid a => fun post => load 2 ctxid a mach post
    | loadWord ctxid a => fun post => load 4 ctxid a mach post
    | loadDouble ctxid a => fun post => load 8 ctxid a mach post
    | storeByte ctxid a v => fun post => store 1 ctxid a v mach (post tt)
    | storeHalf ctxid a v => fun post => store 2 ctxid a v mach (post tt)
    | storeWord ctxid a v => fun post => store 4 ctxid a v mach (post tt)
    | storeDouble ctxid a v => fun post => store 8 ctxid a v mach (post tt)
    | makeReservation _
    | clearReservation _
    | checkReservation _
    | raiseExceptionWithInfo _ _ _ _
        => fun _ => False
    end.
*)

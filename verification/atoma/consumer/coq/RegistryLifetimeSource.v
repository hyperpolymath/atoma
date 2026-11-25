(* SPDX-License-Identifier: MPL-2.0 *)
(* Admitted original destroy body; permission accounting is ghost state, not
   a claim that the current pointer ABI performs lifetime checks. *)
From Coq Require Import List String Bool Arith Lia.
Require Import ScalarSource RegistrySource WrapperSource HeapOwnership.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Record destroy_program := DestroyProgram {
  null_status : nat; busy_status : nat; ok_status : nat }.
Definition canonical := DestroyProgram 4 6 0.
Definition program_eq_dec (a b : destroy_program) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition parse_destroy (tokens : list string) : option destroy_program :=
  match WrapperSource.operands
    [["const";"registry";"=";"r";"orelse";"return"];
     [";";"if";"(";"registry";".";"active";")";"return"];
     [";";"std";".";"heap";".";"c_allocator";".";"destroy";"(";"registry";")";";";"return"];
     [";"]] tokens with
  | Some [n;b;o] => Some (DestroyProgram n b o)
  | _ => None end.
Definition parse (bytes : list nat) : option destroy_program :=
  if WrapperSource.check_registry bytes then
    match WrapperSource.tokenize bytes with
    | Some tokens => match RegistrySource.strip WrapperSource.registry_prefix tokens with
      | Some tail => match RegistrySource.functions WrapperSource.registry_signatures tail with
        | Some [_;destroy;_;_;_] => parse_destroy destroy
        | _ => None end
      | None => None end
    | None => None end
  else None.
Definition check (bytes : list nat) : bool :=
  match parse bytes with
  | Some p => if program_eq_dec p canonical then true else false
  | None => false end.
Lemma accepted_program : forall bytes,
  check bytes = true -> parse bytes = Some canonical.
Proof. intros bytes H; unfold check in H; destruct (parse bytes) as [p|] eqn:E; [|discriminate].
  destruct (program_eq_dec p canonical); [now subst|discriminate]. Qed.

Record endpoint_refs := EndpointRefs { code_region : nat; context_region : option nat }.
Definition endpoint_regions (e : endpoint_refs) :=
  code_region e :: match context_region e with None => [] | Some r => [r] end.
Definition slot_regions (slot : option endpoint_refs) :=
  match slot with None => [] | Some e => endpoint_regions e end.
Definition references (s : RegistrySource.state endpoint_refs) :=
  List.app (slot_regions (RegistrySource.rest s)) (slot_regions (RegistrySource.mcp s)).
Definition retentions (s : RegistrySource.state endpoint_refs) (region : nat) :=
  count_occ Nat.eq_dec (references s) region.
Definition accounted (s : RegistrySource.state endpoint_refs) (h : HeapOwnership.heap) : Prop :=
  forall key, match h key with
  | HeapOwnership.Vacant => retentions s key = 0
  | HeapOwnership.Live _ retained _ => retentions s key <= retained end.

(* Removing registry roots releases THEIR retained obligations. Shared references
   from other registries remain in the global retained count. No endpoint payload
   is destroyed or written by this ghost accounting operation. *)
Definition detach (s : RegistrySource.state endpoint_refs) (h : HeapOwnership.heap) : HeapOwnership.heap :=
  fun key => match h key with
  | HeapOwnership.Vacant => HeapOwnership.Vacant
  | HeapOwnership.Live bytes retained readers =>
      HeapOwnership.Live bytes (retained - retentions s key) readers end.

Record destruction := Destroyed {
  status : nat;
  store : HeapOwnership.heap;
  registration : option (RegistrySource.state endpoint_refs) }.

(* Native interpretation follows null -> active -> allocator.destroy(registry).
   The allocator effect requires the usual valid allocation/authority premise.
   Detachment is the corresponding ghost lifetime effect, not native instructions.
   This function intentionally does not invent a runtime readers/count check. *)
Definition destroy_run (p : destroy_program) (present : bool)
    (s : RegistrySource.state endpoint_refs) (h : HeapOwnership.heap) (addr : nat) : destruction :=
  if negb present then Destroyed (null_status p) h (Some s) else
  if RegistrySource.active s then Destroyed (busy_status p) h (Some s) else
  Destroyed (ok_status p) (detach s (HeapOwnership.replace h addr HeapOwnership.Vacant)) None.

Theorem null_refuses : forall p s h addr,
  destroy_run p false s h addr = Destroyed (null_status p) h (Some s).
Proof. reflexivity. Qed.
Theorem busy_preserves : forall p s h addr,
  RegistrySource.active s = true ->
  destroy_run p true s h addr = Destroyed (busy_status p) h (Some s).
Proof. intros p s h addr H; unfold destroy_run; simpl; now rewrite H. Qed.
Theorem idle_release : forall p s h addr bytes,
  RegistrySource.active s = false -> h addr = HeapOwnership.Live bytes 0 0 ->
  status (destroy_run p true s h addr) = ok_status p /\
  forall key, store (destroy_run p true s h addr) key =
    detach s (snd (HeapOwnership.run HeapOwnership.Release h addr)) key.
Proof. intros p s h addr bytes Hidle Howned; unfold destroy_run; cbn [negb]; rewrite Hidle.
  split; [reflexivity|]. intro key; unfold HeapOwnership.run; rewrite Howned; reflexivity. Qed.
Theorem other_allocation_live : forall p s h addr key bytes retained readers,
  RegistrySource.active s = false -> key <> addr -> accounted s h ->
  h key = HeapOwnership.Live bytes retained readers ->
  exists remaining, store (destroy_run p true s h addr) key = HeapOwnership.Live bytes remaining readers /\
    remaining + retentions s key = retained.
Proof.
  intros p s h addr key bytes retained readers Hidle Hneq Haccount Hlive.
  pose proof (Haccount key) as Hcount; rewrite Hlive in Hcount; simpl in Hcount.
  unfold destroy_run; cbn [negb]; rewrite Hidle; cbn [store].
  unfold detach, HeapOwnership.replace; destruct (Nat.eq_dec key addr); [contradiction|].
  rewrite Hlive; exists (retained - retentions s key); split; [reflexivity|].
  now apply Nat.sub_add.
Qed.
Theorem detaches_registrations : forall p s h addr,
  RegistrySource.active s = false -> registration (destroy_run p true s h addr) = None.
Proof. intros p s h addr H; unfold destroy_run; cbn [negb]; now rewrite H. Qed.

(* Source-facing contracts require a live mapped registry allocation. The caller
   additionally owes correspondence between s and the native registry payload;
   the byte representation/layout and raw-pointer provenance are not derived by
   this model. Distinct region IDs express assumed native separation. *)
Theorem source_idle_release : forall bytes,
  check bytes = true -> exists p, parse bytes = Some p /\
  forall s h addr payload,
    RegistrySource.active s = false -> h addr = HeapOwnership.Live payload 0 0 -> accounted s h ->
    status (destroy_run p true s h addr) = 0 /\
    forall key, store (destroy_run p true s h addr) key =
      detach s (snd (HeapOwnership.run HeapOwnership.Release h addr)) key.
Proof. intros bytes H; exists canonical; split; [now apply accepted_program|].
  intros; now apply idle_release. Qed.
Theorem source_busy_preserves : forall bytes,
  check bytes = true -> exists p, parse bytes = Some p /\
  forall s h addr payload retained readers,
    h addr = HeapOwnership.Live payload retained readers -> RegistrySource.active s = true ->
    destroy_run p true s h addr = Destroyed 6 h (Some s).
Proof. intros bytes H; exists canonical; split; [now apply accepted_program|].
  intros; now apply busy_preserves. Qed.
Theorem source_other_allocation_live : forall bytes,
  check bytes = true -> exists p, parse bytes = Some p /\
  forall s h addr key registry_payload payload retained readers,
    h addr = HeapOwnership.Live registry_payload 0 0 ->
    RegistrySource.active s = false -> key <> addr -> accounted s h ->
    h key = HeapOwnership.Live payload retained readers ->
    exists remaining, store (destroy_run p true s h addr) key = HeapOwnership.Live payload remaining readers /\
      remaining + retentions s key = retained.
Proof. intros bytes H; exists canonical; split; [now apply accepted_program|].
  intros; now apply other_allocation_live. Qed.
Theorem source_detaches_registrations : forall bytes,
  check bytes = true -> exists p, parse bytes = Some p /\
  forall s h addr payload, h addr = HeapOwnership.Live payload 0 0 ->
    accounted s h -> RegistrySource.active s = false ->
    registration (destroy_run p true s h addr) = None.
Proof. intros bytes H; exists canonical; split; [now apply accepted_program|].
  intros; now apply detaches_registrations. Qed.

(* Two slots share one context; an unrelated owner's retention must survive.
   The registry is region 0, code regions 1/2, context region 9. *)
Definition shared_endpoints := RegistrySource.State
  (Some (EndpointRefs 1 (Some 9))) (Some (EndpointRefs 2 (Some 9))) false.
Definition shared_heap (key : nat) : HeapOwnership.allocation :=
  match key with
  | 0 => HeapOwnership.Live [42] 0 0
  | 1 | 2 => HeapOwnership.Live [] 1 0
  | 9 => HeapOwnership.Live [7] 3 0
  | _ => HeapOwnership.Vacant end.
Example shared_context_count : retentions shared_endpoints 9 = 2.
Proof. reflexivity. Qed.
Example shared_context_survives_destroy :
  store (destroy_run canonical true shared_endpoints shared_heap 0) 9 = HeapOwnership.Live [7] 1 0.
Proof. reflexivity. Qed.
Example registry_removed :
  store (destroy_run canonical true shared_endpoints shared_heap 0) 0 = HeapOwnership.Vacant.
Proof. reflexivity. Qed.

Print Assumptions source_idle_release.
Print Assumptions source_busy_preserves.
Print Assumptions source_other_allocation_live.
Print Assumptions source_detaches_registrations.

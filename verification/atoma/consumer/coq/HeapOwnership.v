(* SPDX-License-Identifier: MPL-2.0 *)
(* Ghost permissions. Native pointer/region correspondence and authority are premises. *)
From Coq Require Import List Arith Bool Lia.
Import ListNotations.

Inductive allocation := Vacant | Live (bytes : list nat) (retained readers : nat).
Inductive operation := Acquire (bytes : list nat) | Retain | DropRetention |
  BorrowRead | ReturnRead | Release | WriteBytes (bytes : list nat).
Definition cell_step (op : operation) (cell : allocation) : option allocation :=
  match op, cell with
  | Acquire bytes, Vacant => Some (Live bytes 0 0)
  | Retain, Live bytes retained readers => Some (Live bytes (S retained) readers)
  | DropRetention, Live bytes (S retained) readers => Some (Live bytes retained readers)
  | BorrowRead, Live bytes retained readers => Some (Live bytes retained (S readers))
  | ReturnRead, Live bytes retained (S readers) => Some (Live bytes retained readers)
  | Release, Live _ 0 0 => Some Vacant
  | WriteBytes bytes, Live _ retained 0 => Some (Live bytes retained 0)
  | _, _ => None
  end.
Definition heap := nat -> allocation.
Definition replace (h : heap) (addr : nat) (value : allocation) : heap :=
  fun key => if Nat.eq_dec key addr then value else h key.
Definition run (op : operation) (h : heap) (addr : nat) : bool * heap :=
  match cell_step op (h addr) with
  | None => (false,h)
  | Some value => (true,replace h addr value)
  end.
Definition read_bytes (cell : allocation) : option (list nat) :=
  match cell with Vacant => None | Live bytes _ _ => Some bytes end.
Definition then_cell (first second : operation) (cell : allocation) :=
  match cell_step first cell with None => None | Some next => cell_step second next end.
Definition bytes_after (op : operation) (cell : allocation) :=
  match cell_step op cell with None => None | Some next => read_bytes next end.

Theorem release_borrowed_refused : forall bytes retained readers,
  cell_step Release (Live bytes retained (S readers)) = None.
Proof. intros; destruct retained; reflexivity. Qed.
Theorem release_retained_refused : forall bytes retained readers,
  cell_step Release (Live bytes (S retained) readers) = None.
Proof. reflexivity. Qed.
Theorem write_borrowed_refused : forall bytes old retained readers,
  cell_step (WriteBytes bytes) (Live old retained (S readers)) = None.
Proof. reflexivity. Qed.
Theorem failed_preserves : forall op h addr key,
  cell_step op (h addr) = None -> snd (run op h addr) key = h key.
Proof. intros op h addr key H; unfold run; now rewrite H. Qed.
Theorem borrow_return_cell : forall bytes retained readers,
  then_cell BorrowRead ReturnRead (Live bytes retained readers) = Some (Live bytes retained readers).
Proof. reflexivity. Qed.
Theorem borrow_preserves_bytes : forall bytes retained readers,
  bytes_after BorrowRead (Live bytes retained readers) = read_bytes (Live bytes retained readers).
Proof. reflexivity. Qed.
Theorem release_removes_owned : forall h addr bytes,
  h addr = Live bytes 0 0 -> snd (run Release h addr) addr = Vacant.
Proof. intros h addr bytes H; unfold run; rewrite H; simpl; unfold replace.
  destruct (Nat.eq_dec addr addr); [reflexivity|contradiction]. Qed.
Theorem release_frames_other : forall h addr key bytes,
  h addr = Live bytes 0 0 -> key <> addr -> snd (run Release h addr) key = h key.
Proof. intros h addr key bytes H Hneq; unfold run; rewrite H; simpl; unfold replace.
  destruct (Nat.eq_dec key addr); [contradiction|reflexivity]. Qed.
Theorem acquire_live_refused : forall bytes old retained readers,
  cell_step (Acquire bytes) (Live old retained readers) = None.
Proof. reflexivity. Qed.

Definition span_fits (offset count : nat) (bytes : list nat) : bool :=
  offset + count <=? List.length bytes.
Definition borrowed_span (offset count : nat) (bytes : list nat) :=
  firstn count (skipn offset bytes).
Theorem span_length : forall offset count bytes,
  span_fits offset count bytes = true -> List.length (borrowed_span offset count bytes) = count.
Proof. intros offset count bytes H; unfold span_fits in H; apply Nat.leb_le in H.
  unfold borrowed_span; rewrite firstn_length, skipn_length; apply Nat.min_l; lia. Qed.

Print Assumptions release_borrowed_refused.
Print Assumptions release_retained_refused.
Print Assumptions write_borrowed_refused.
Print Assumptions failed_preserves.
Print Assumptions borrow_return_cell.
Print Assumptions borrow_preserves_bytes.
Print Assumptions release_removes_owned.
Print Assumptions release_frames_other.
Print Assumptions acquire_live_refused.
Print Assumptions span_length.

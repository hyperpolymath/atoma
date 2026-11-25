#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
[[ $# == 3 ]]
for source in "$@"; do [[ -f $source && $(wc -c < "$source") -le 65536 ]]; done
cat <<'COQ'
From Coq Require Import List Bool Arith ZArith.
Require Import HeaderBoundarySource WrapperSource HeapOwnership.
Import ListNotations.
Open Scope nat_scope.
COQ
bytes() {
  printf 'Definition %s : list nat := ' "$1"
  od -An -v -tu1 "$2" | awk 'BEGIN {printf "["} {for(i=1;i<=NF;i++) {if(n++) printf ";"; printf "%s",$i}} END {print "]."}'
}
bytes core_bytes "$1"
bytes export_bytes "$2"
bytes backend_bytes "$3"
cat <<'COQ'
Lemma entry_accepted : HeaderBoundarySource.check core_bytes export_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma backend_accepted : WrapperSource.check_header backend_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Theorem source_null_checked : forall h addr offset count tls backend,
  exists p, HeaderBoundarySource.parse_core core_bytes = Some p /\
  HeaderBoundarySource.check_export export_bytes = true /\
  HeaderBoundarySource.run p false h addr offset count tls backend =
    Some (HeaderBoundarySource.Observe (-1)%Z false h tls []).
Proof. intros; eapply HeaderBoundarySource.source_null; exact entry_accepted. Qed.
Theorem source_normal_checked : forall h addr offset count tls backend bytes retained readers,
  h addr = HeapOwnership.Live bytes retained (S readers) ->
  HeapOwnership.span_fits offset count bytes = true ->
  HeaderBoundarySource.backend_frames addr backend ->
  exists p, HeaderBoundarySource.parse_core core_bytes = Some p /\
  HeaderBoundarySource.check_export export_bytes = true /\
  exists observed, HeaderBoundarySource.run p true h addr offset count tls backend = Some observed /\
    HeaderBoundarySource.calls observed = [HeapOwnership.borrowed_span offset count bytes] /\
    HeaderBoundarySource.final_heap observed addr = h addr /\
    HeapOwnership.cell_step HeapOwnership.ReturnRead (HeaderBoundarySource.final_heap observed addr) =
      Some (HeapOwnership.Live bytes retained readers).
Proof. intros; eapply HeaderBoundarySource.source_normal; eauto using entry_accepted. Qed.
Theorem source_result_checked : forall h addr offset count tls effect bytes retained readers step foreign,
  h addr = HeapOwnership.Live bytes retained (S readers) ->
  HeapOwnership.span_fits offset count bytes = true ->
  Forall (fun b => b < 256) (HeapOwnership.borrowed_span offset count bytes) ->
  (forall s b, b < 256 -> foreign (WrapperSource.encode s) b = Some (WrapperSource.encode (step s b))) ->
  exists p, HeaderBoundarySource.parse_core core_bytes = Some p /\
  HeaderBoundarySource.check_export export_bytes = true /\
  exists observed, HeaderBoundarySource.run p true h addr offset count tls
    (HeaderBoundarySource.interpreted_backend foreign effect) = Some observed /\
    HeaderBoundarySource.status observed = 0%Z /\ HeaderBoundarySource.value observed =
      WrapperSource.fold step false (HeapOwnership.borrowed_span offset count bytes).
Proof.
  intros; eapply HeaderBoundarySource.source_fold;
    eauto using entry_accepted, backend_accepted.
  unfold HeaderBoundarySource.implements_scan, HeaderBoundarySource.interpreted_backend; reflexivity.
Qed.
Print Assumptions source_null_checked.
Print Assumptions source_normal_checked.
Print Assumptions source_result_checked.
Print Assumptions backend_accepted.
COQ

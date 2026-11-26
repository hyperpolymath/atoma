#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
[[ $# == 3 ]]
for source in "$@"; do [[ -f $source && $(wc -c < "$source") -le 65536 ]]; done
cat <<'COQ'
From Coq Require Import List Bool String.
Require Import ScalarSource RegistrySource WrapperSource HeapOwnership RegistryLifetimeSource.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
COQ
bytes() {
  printf 'Definition %s : list nat := ' "$1"
  od -An -v -tu1 "$2" | awk 'BEGIN {printf "["} {for(i=1;i<=NF;i++) {if(n++) printf ";"; printf "%s",$i}} END {print "]."}'
}
bytes registry_bytes "$1"
bytes dependency_bytes "$2"
bytes protocol_bytes "$3"
cat <<'COQ'
Lemma source_accepted : RegistryLifetimeSource.check registry_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dependency_accepted : RegistrySource.check dependency_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Definition protocol_exports_known : bool :=
  match ScalarSource.lex (List.length protocol_bytes) protocol_bytes with
  | Some ("pub" :: "fn" :: "known" :: _) => true
  | _ => false end.
Lemma protocol_accepted : protocol_exports_known = true /\
  ScalarSource.parse protocol_bytes = Some (ScalarSource.inclusive_range 1 9).
Proof. vm_compute. split; reflexivity. Qed.
Theorem source_idle_release : exists p, RegistryLifetimeSource.parse registry_bytes = Some p /\
  forall s h addr payload,
    RegistrySource.active s = false -> h addr = HeapOwnership.Live payload 0 0 -> RegistryLifetimeSource.accounted s h ->
    RegistryLifetimeSource.status (RegistryLifetimeSource.destroy_run p true s h addr) = 0 /\
    forall key, RegistryLifetimeSource.store (RegistryLifetimeSource.destroy_run p true s h addr) key =
      RegistryLifetimeSource.detach s (snd (HeapOwnership.run HeapOwnership.Release h addr)) key.
Proof. apply RegistryLifetimeSource.source_idle_release; exact source_accepted. Qed.
Theorem source_busy_preserves : exists p, RegistryLifetimeSource.parse registry_bytes = Some p /\
  forall s h addr payload retained readers,
    h addr = HeapOwnership.Live payload retained readers -> RegistrySource.active s = true ->
    RegistryLifetimeSource.destroy_run p true s h addr = RegistryLifetimeSource.Destroyed 6 h (Some s).
Proof. apply RegistryLifetimeSource.source_busy_preserves; exact source_accepted. Qed.
Theorem source_other_allocation_live : exists p, RegistryLifetimeSource.parse registry_bytes = Some p /\
  forall s h addr key registry_payload payload retained readers,
    h addr = HeapOwnership.Live registry_payload 0 0 ->
    RegistrySource.active s = false -> key <> addr -> RegistryLifetimeSource.accounted s h ->
    h key = HeapOwnership.Live payload retained readers ->
    exists remaining, RegistryLifetimeSource.store (RegistryLifetimeSource.destroy_run p true s h addr) key =
      HeapOwnership.Live payload remaining readers /\ remaining + RegistryLifetimeSource.retentions s key = retained.
Proof. apply RegistryLifetimeSource.source_other_allocation_live; exact source_accepted. Qed.
Theorem source_detaches_registrations : exists p, RegistryLifetimeSource.parse registry_bytes = Some p /\
  forall s h addr payload, h addr = HeapOwnership.Live payload 0 0 ->
    RegistryLifetimeSource.accounted s h -> RegistrySource.active s = false ->
    RegistryLifetimeSource.registration (RegistryLifetimeSource.destroy_run p true s h addr) = None.
Proof. apply RegistryLifetimeSource.source_detaches_registrations; exact source_accepted. Qed.
Print Assumptions source_idle_release.
Print Assumptions source_busy_preserves.
Print Assumptions source_other_allocation_live.
Print Assumptions source_detaches_registrations.
Print Assumptions dependency_accepted.
Print Assumptions protocol_accepted.
COQ

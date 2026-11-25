#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
[[ $# == 4 && -f $2 && -f $3 ]]
profile=$1
[[ $profile == registry || $profile == header ]]
for source in "$2" "$3"; do [[ $(wc -c < "$source") -le 65536 ]]; done
cat <<'COQ'
From Coq Require Import List Bool ZArith.
Require Import WrapperSource RegistrySource.
Import ListNotations.
Open Scope nat_scope.
COQ
bytes() {
  printf 'Definition %s : list nat := ' "$1"
  od -An -v -tu1 "$2" | awk 'BEGIN {printf "["} {for(i=1;i<=NF;i++) {if(n++) printf ";"; printf "%s",$i}} END {print "]."}'
}
bytes wrapper_bytes "$2"
bytes dependency_bytes "$3"
if [[ $profile == registry ]]; then
[[ -f $4 && $(wc -c < "$4") -le 65536 ]]
bytes protocol_bytes "$4"
cat <<'COQ'
Lemma source_accepted : WrapperSource.check_registry wrapper_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dependency_accepted : RegistrySource.check dependency_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma protocol_accepted : ScalarSource.parse protocol_bytes = Some (ScalarSource.inclusive_range 1 9).
Proof. vm_compute. reflexivity. Qed.
Theorem source_checked : forall A present (s : RegistrySource.state A) tag valid callback,
  RegistrySource.active s = false -> WrapperSource.callback_frames callback ->
  exists p, WrapperSource.parse_registry wrapper_bytes = Some p /\
    WrapperSource.final_registry (WrapperSource.registry_run p present s tag valid callback) = s.
Proof. intros. eapply WrapperSource.registry_normal_frame; eauto using source_accepted. Qed.
Print Assumptions source_checked.
Print Assumptions dependency_accepted.
Print Assumptions protocol_accepted.
COQ
else
# The pointer carrier / RefC runtime remain an explicit call contract. Preserve
# their actual bytes in the capsule rather than pretending this is a proof of them.
cat <<'COQ'
Lemma source_accepted : WrapperSource.check_header wrapper_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Theorem source_checked : forall step foreign bs,
  Forall (fun b => b < 256) bs ->
  (forall s b, b < 256 -> foreign (WrapperSource.encode s) b = Some (WrapperSource.encode (step s b))) ->
  exists p, WrapperSource.parse_header wrapper_bytes = Some p /\
    WrapperSource.header_run p foreign bs = Some (WrapperSource.fold step false bs).
Proof. intros. eapply WrapperSource.header_source_fold; eauto using source_accepted. Qed.
Print Assumptions source_checked.
COQ
fi

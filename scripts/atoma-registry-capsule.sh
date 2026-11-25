#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
[[ $# == 1 && -f "$1" && $(wc -c < "$1") -le 65536 ]] || exit 2
cat <<'COQ'
From Coq Require Import List Bool ZArith.
Require Import RegistrySource.
Import ListNotations.
Open Scope nat_scope.
COQ
printf 'Definition source_bytes : list nat := '
od -An -v -tu1 "$1" | awk 'BEGIN {printf "["} {for(i=1;i<=NF;i++) {if(n++) printf ";"; printf "%s",$i}} END {print "]."}'
cat <<'COQ'
Lemma source_accepted : RegistrySource.check source_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Theorem source_checked : exists p, RegistrySource.parse source_bytes = Some p /\
  (forall A (s : RegistrySource.state A) k e, RegistrySource.register p s k e = RegistrySource.spec_register s k e) /\
  (forall A (s : RegistrySource.state A) k, RegistrySource.unregister p s k = RegistrySource.spec_unregister s k) /\
  (forall A (s : RegistrySource.state A) k, RegistrySource.begin p s k = RegistrySource.spec_begin s k) /\
  (forall A (s : RegistrySource.state A), RegistrySource.finish p s = RegistrySource.busy_state s false) /\
  (forall z, RegistrySource.sanitize p z = if (0 <=? z)%Z && (z <=? 11)%Z then z else 6%Z).
Proof. apply RegistrySource.source_refines. exact source_accepted. Qed.
Print Assumptions source_checked.
COQ

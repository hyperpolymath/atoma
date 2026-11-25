#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail
[[ $# == 2 ]] || { echo 'usage: atoma-word-capsule.sh DECODER ENCODER' >&2; exit 2; }
for input in "$@"; do
    [[ -f "$input" && $(wc -c < "$input") -le 65536 ]] || exit 2
done
bytes() {
    od -An -v -tu1 "$1" | awk 'BEGIN {printf "["} {for(i=1;i<=NF;i++) {if(n++) printf ";"; printf "%s",$i}} END {print "]."}'
}
cat <<'COQ'
From Coq Require Import List NArith.
Require Import WordSource.
Import ListNotations.
Open Scope nat_scope.
COQ
printf 'Definition decoder_bytes : list nat := '
bytes "$1"
printf 'Definition encoder_bytes : list nat := '
bytes "$2"
cat <<'COQ'
Lemma source_accepted : WordSource.check decoder_bytes encoder_bytes = true.
Proof. vm_compute. reflexivity. Qed.
Theorem source_checked : forall w b,
  WordSource.run decoder_bytes encoder_bytes w = Some (Some b) <->
  (b < 256)%N /\ w = CanonicalWord.encode b.
Proof. apply WordSource.source_exact. exact source_accepted. Qed.
Theorem source_no_trap : forall w,
  WordSource.run decoder_bytes encoder_bytes w = Some (CanonicalWord.decode w).
Proof. apply WordSource.source_corresponds. exact source_accepted. Qed.
Print Assumptions source_checked.
Print Assumptions source_no_trap.
COQ

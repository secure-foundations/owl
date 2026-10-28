#!/bin/bash
# Checks that the IKEv2 proof is not vacuous: each mutant below weakens the
# code, a guarantee or a proof step, and Owl must reject every one of them.
# Run from anywhere; takes a few minutes.

set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cd "$REPO"
OWL=$(cabal list-bin owl)
failed=0

# mutant NAME FILE OLD NEW [FILE_TO_CHECK]
mutant() {
    local name=$1 file=$2 old=$3 new=$4 tgt=${5:-$2}
    rm -f "$WORK"/*.owl "$WORK"/*.smtcache
    cp "$HERE"/*.owl "$WORK"/
    python3 - "$WORK/$file" "$old" "$new" <<'EOF' || { echo "BAD PATTERN: $name"; failed=1; return; }
import sys
p, o, n = sys.argv[1:]
s = open(p).read()
assert o in s
open(p, "w").write(s.replace(o, n, 1))
EOF
    if "$OWL" "$WORK/$tgt" >/dev/null 2>&1; then
        echo "SURVIVED: $name"; failed=1
    else
        echo "killed:   $name"
    fi
}

mutant "init: success unreachable" init.owl "    Some(packed)" "    assert(false); Some(packed)"
mutant "resp: success unreachable" resp.owl "    Some(packed)" "    assert(false); Some(packed)"
mutant "init: no eq check after vrfy" init.owl "    guard eq(x, octets_r) in" ""
mutant "resp: no eq check after vrfy" resp.owl "    guard eq(x, octets_i) in" ""
mutant "init: no corr_case skR" init.owl "    corr_case skR<@m> in" ""
mutant "resp: no corr_case skI" resp.owl "    corr_case skI<@n> in" ""
mutant "resp: signs KEi in place of KEr" resp.owl \
    "resp_octets(spi_i, spi_r, ke_r, nr, ni, maced_id_r)" "resp_octets(spi_i, spi_r, ke_i, nr, ni, maced_id_r)"
mutant "init: signs KEr in place of KEi" init.owl \
    "init_octets(spi_i, ke_i, ni, nr, maced_id_i)" "init_octets(spi_i, ke_r, ni, nr, maced_id_i)"
mutant "defs: child keys secret without sec(E_r)" defs.owl \
    "sec(E_i<i@n>) /\\ sec(E_r<j@m>)" "sec(E_i<i@n>)" init.owl
mutant "defs: child keys secret without sec(E_i)" defs.owl \
    "sec(E_i<i@n>) /\\ sec(E_r<j@m>)" "sec(E_r<j@m>)" resp.owl
mutant "defs: initiator authenticates without sec(skR)" defs.owl \
    "ir_ke_r : (x:Ghost{sec(skR<@m>) ==>" "ir_ke_r : (x:Ghost{true ==>" init.owl
mutant "defs: responder authenticates without sec(skI)" defs.owl \
    "rr_ke_i : (x:Ghost{sec(skI<@n>) ==>" "rr_ke_i : (x:Ghost{true ==>" resp.owl
mutant "init: child keys from SK_ei" init.owl \
    "enckey||enckey; 0>(sk_d, 0x, s)" "enckey||enckey; 0>(sk_ei, 0x, s)"
mutant "init: no pcase on KEr" init.owl "    pcase is_e_r[ke_r] in" ""
mutant "resp: no pcase on KEi" resp.owl "    pcase is_e_i[ke_i] in" ""
mutant "init: no cross_dh_lemma" init.owl "    cross_dh_lemma<E_i<i@n>>(ke_r);" ""

exit $failed

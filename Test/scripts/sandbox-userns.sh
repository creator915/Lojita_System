#!/usr/bin/env bash
# Verify ordinary-UID operation, including Ubuntu hosts with restricted user namespaces.
set -euo pipefail
[[ $EUID == 0 ]] || { echo "Loading the temporary AppArmor test profile requires root." >&2; exit 1; }
restriction=$(cat /proc/sys/kernel/apparmor_restrict_unprivileged_userns 2>/dev/null || echo 0)
scratch=$(mktemp -d /var/lib/lojita-g4-userns.XXXXXXXX)
name=${scratch##*/}
uid=60001
cleanup() {
  if [[ $restriction == 1 ]] && grep -qF "$name " /sys/kernel/security/apparmor/profiles; then
    apparmor_parser -K -R "$scratch/profile" || return 1
    if grep -qF "$name " /sys/kernel/security/apparmor/profiles; then return 1; fi
  fi
  rm -rf -- "$scratch"
}
trap 'cleanup || exit 1' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
# Only root can replace this launcher. The unprivileged driver owns a separate staging directory.
chgrp "$uid" "$scratch"
chmod 0750 "$scratch"
install -o root -g "$uid" -m 0750 "$1" "$scratch/launcher"
install -o root -g "$uid" -m 0750 "$2" "$scratch/probe"
install -d -o "$uid" -g "$uid" -m 0700 "$scratch/stage"
cat > "$scratch/profile" <<EOF
abi <abi/4.0>,
profile $name $scratch/launcher flags=(unconfined) {
  userns,
}
EOF
# Stage the test tools before dropping privilege, including on private checkouts.
lake build test-sandbox-owned
install -m 0755 .lake/build/bin/test-sandbox-owned "$scratch/owned"
install -Dm 0644 Test/scripts/sandbox-gates.py "$scratch/Test/scripts/sandbox-gates.py"
install -Dm 0644 Lojita/Store/TreeCAS/objects.py "$scratch/Lojita/Store/TreeCAS/objects.py"
if [[ $restriction == 1 ]]; then apparmor_parser -K -a "$scratch/profile"; fi
ordinary=(setpriv --reuid="$uid" --regid="$uid" --clear-groups env -i PATH=/usr/bin:/bin HOME="$scratch/stage" TMPDIR="$scratch/stage" LC_ALL=C)
"${ordinary[@]}" python3 -c 'import os; assert os.geteuid() == 60001; assert int(open("/proc/self/status").read().split("CapEff:")[1].split()[0],16) == 0'
"${ordinary[@]}" python3 "$scratch/Test/scripts/sandbox-gates.py" "$scratch/launcher" "$scratch/probe"
"${ordinary[@]}" "$scratch/owned" "$scratch/launcher" "$scratch/probe"
[[ -z $(find "$scratch/stage" -mindepth 1 -print -quit) ]]
[[ $(cat /proc/sys/kernel/apparmor_restrict_unprivileged_userns 2>/dev/null || echo 0) == "$restriction" ]]
cleanup
trap - EXIT
echo "UID $uid passed the native and Lean sandbox gates. Host user namespace policy and temporary staging were restored."

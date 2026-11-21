#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"

scratch=$(mktemp -d "${TMPDIR:-/tmp}/codetransport-namespace.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/host" "$scratch/generated"

# check.sh 让 Agda 把接口写在源文件旁。在临时源码副本中执行两次检查。
cp --parents -t "$scratch/host" check.sh Code.agda Code/*.agda Ownership.agda \
  OwnershipIO.agda OwnershipIO/*.agda Test/NamespaceTest.agda
cd "$scratch/host"
./check.sh Code/Namespace.agda
./check.sh Test/NamespaceTest.agda
agda --compile --ghc-flag=-O0 --compile-dir="$scratch/build" \
  -i . -i /usr/share/agda-stdlib Test/NamespaceTest.agda >"$scratch/build.log" 2>&1 || {
  cat "$scratch/build.log" >&2
  exit 1
}

cd "$scratch/generated"
"$scratch/build/NamespaceTest"

expect_source() {
  if ! grep -Fq -- "$2" "$1"; then
    printf '在 %s 中找不到 %s\n' "$1" "$2" >&2
    return 1
  fi
}

expect_source Gen/T1_r1/Root/Parser.agda 'import Gen.T1_r1.Root.Parser.Helper as Helper'
expect_source Gen/T1_r1/Root/Engine.agda 'import Gen.T1_r1.Root.Engine.Helper as Helper'
agda --safe --no-libraries -i . Gen/T1_r1/Root.agda

expect_source Gen/T1_r2/Root/Engine.agda 'import Gen.T1_r1.Root.Engine as OldEngine'
expect_source Gen/T1_r2/Root/Engine.agda 'OldEngine.run x ≡ run x'
expect_source Gen/T1_r2/Root/Engine.agda 'commutes x = refl'
agda --safe --no-libraries -i . Gen/T1_r2/Root/Engine.agda
printf '%s\n' 'PASS 同树两个 Helper 与跨版本 Engine 交换图均已通过 Agda 检查。'

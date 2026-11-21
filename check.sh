#!/bin/bash
# 用法: ./check.sh File.agda   —— 只显示本仓库文件的报错，stdlib 的 cubical 警告过滤掉
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
if [ "$#" -eq 0 ]; then
  exec python3 scripts/verify_modules.py check
fi
out=$(agda -i . -i /usr/share/agda-stdlib "$1" 2>&1)
code=$?
# 从第一个本仓库路径（非 stdlib）开始打印，去掉 stdlib 警告块
echo "$out" | awk -v repo="$PWD/" '
  /^\/usr\/share\/agda-stdlib/ { skip=1; next }
  index($0, repo) == 1          { skip=0 }
  /^Checking/                   { skip=0 }
  /All done/                    { skip=0 }
  /^Data\.List\./               { next }
  /^Function\./                 { next }
  skip==1                       { next }
  /^$/                          { next }
  /yet supported|injectivity|Cubical|not compute when applied|when checking the definition of|^Reason|^This clause/ { next }
  { print }
'
if [ $code -eq 0 ]; then echo "== OK: $1"; else echo "== FAILED ($code): $1"; fi
exit $code

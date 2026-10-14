#!/usr/bin/env bash
set -euo pipefail

# This script runs inside the pinned TeX Live Alpine image used by both PR
# validation and the production documentation workflow. Pin the primary Alpine
# build tools as well, so repository updates fail closed instead of silently
# changing the Blueprint toolchain. Transitive APK dependencies still come from
# the Alpine v3.21 repositories; a fully hermetic build would require a custom
# immutable image containing these tools.
apk add --no-cache \
  'py3-pip=24.3.1-r0' \
  'python3=3.12.15-r0' \
  'python3-dev=3.12.15-r0' \
  'git=2.47.3-r0' \
  'pkgconf=2.3.0-r0' \
  'graphviz=12.2.0-r0' \
  'graphviz-dev=12.2.0-r0' \
  'gcc=14.2.0-r4' \
  'musl-dev=1.2.5-r11'

git config --global --add safe.directory "$GITHUB_WORKSPACE"
git config --global --add safe.directory "$(pwd)"

python3 -m venv env
source env/bin/activate
python -m pip install --no-cache-dir --upgrade \
  'pip==26.2.1' \
  'wheel==0.48.0' \
  'packaging==26.3'
python -m pip install --no-cache-dir 'pygraphviz==2.0.3' \
  --config-settings="--global-option=build_ext" \
  --config-settings="--global-option=-L/usr/lib/graphviz/" \
  --config-settings="--global-option=-R/usr/lib/graphviz/"
python -m pip install --no-cache-dir -r blueprint/requirements-ci.txt
python -m pip check

python3 -m unittest discover -s scripts/tests -v
python3 scripts/blueprint_status.py --milestones

leanblueprint pdf
leanblueprint web

mkdir -p home_page
cp blueprint/print/print.pdf home_page/blueprint.pdf
rm -rf home_page/blueprint
cp -r blueprint/web home_page/blueprint

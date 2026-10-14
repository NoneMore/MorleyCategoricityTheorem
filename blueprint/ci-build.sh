#!/usr/bin/env bash
set -euo pipefail

# This script runs inside the pinned TeX Live Alpine image used by both PR
# validation and the production documentation workflow.
apk add --no-cache py3-pip git pkgconfig graphviz graphviz-dev gcc musl-dev

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

leanblueprint pdf
leanblueprint web

mkdir -p home_page
cp blueprint/print/print.pdf home_page/blueprint.pdf
rm -rf home_page/blueprint
cp -r blueprint/web home_page/blueprint

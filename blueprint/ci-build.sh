#!/usr/bin/env bash
set -euo pipefail

# This script runs inside the digest-pinned TeX Live image (Alpine v3.21)
# shared by PR validation and documentation publishing. Alpine repositories
# replace package patch/revision builds in place, so pinning exact APK revisions
# here would eventually make even an unchanged commit unbuildable. Restrict the
# Python minor version required by the virtualenv and resolve available security
# and patch updates within the image's fixed Alpine release branch.
# The Python application dependencies remain pinned in requirements-ci.txt.
# For a fully hermetic system toolchain, preinstall these APKs in an immutable
# custom image and pin that image by digest instead.
apk add --no-cache --upgrade \
  py3-pip \
  'python3=~3.12' \
  'python3-dev=~3.12' \
  git \
  pkgconf \
  graphviz \
  graphviz-dev \
  gcc \
  musl-dev

# Record resolved native packages to make future environment drift diagnosable.
apk info -v python3 python3-dev git graphviz graphviz-dev gcc

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

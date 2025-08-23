#! /usr/bin/env sh
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
HOL_LIGHT_DIR="/workspaces/hol-light-devcontainer/hol-light"

exec "$HOL_LIGHT_DIR/hol.sh" <<EOF
load_path := "$SCRIPT_DIR" :: !load_path;;
loadt "make.ml";;
loadt "tests.ml";;
EOF

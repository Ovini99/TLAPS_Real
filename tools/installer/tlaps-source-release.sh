#!/bin/bash

TLAPSVER=$(echo "tlaps-1.5.0" | sed -e 's/ /_/g')
TARGET="`/bin/pwd`/$TLAPSVER.tar.gz"

PS_DIR="$(pwd)/../../../tlaps"
PM_DIR="$(pwd)/../.."

cat <<EOF

This script builds a source distribution of the TLA+ Proof System
version 1.5.0.

Target: ${TARGET}
SVN branch: ${SVN_PATH}

EOF

function git_export() {
    (cd "$1" && git archive --format=tar HEAD "$2") | tar xf -
}

################################################################################

TLAPS_DIR="/tmp/$TLAPSVER"

rm -rf "$TLAPS_DIR"
mkdir -p "$TLAPS_DIR"
cd "$TLAPS_DIR"
git_export "$PS_DIR" isabelle
( mkdir tlapm && cd tlapm && git_export "$PM_DIR" . )
rm -rf tlapm/bugs tlapm/bugs-archive tlapm/fixed-bugs tlapm/doc \
       tlapm/examples-draft
git_export "$PS_DIR" zenon
( mkdir emacs && cd emacs && git_export "$PS_DIR/misc" tla-mode )
cd ..
tar -czf "$TARGET" "$TLAPSVER"

cat <<EOF

Created: $TARGET

EOF

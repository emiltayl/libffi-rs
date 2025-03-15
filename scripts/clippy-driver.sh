#!/bin/sh
# Utility script to get clippy lints of doctests to return an error code on any findings

set -eu

exec clippy-driver ${CLIPPYFLAGS} $@
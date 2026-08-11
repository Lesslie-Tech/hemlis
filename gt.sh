#!/usr/bin/env bash
# Regenerate golden-test baselines by running the in-tree harness in overwrite
# mode. No external `goldentests` binary required.
GOLDENTESTS_OVERWRITE=1 cargo test --test goldentests

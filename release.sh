#!/usr/bin/env bash

TAG=$1

if [[ -z "$1" ]]; then
    echo "Usage: ./release.sh <tag>"
    exit 1
fi

if [[ -n "$(git status --short)" ]]; then
    echo "You have unstaged changes, a clean environment is required"
    exit 1
fi

if [[ "$(git rev-parse --abbrev-ref HEAD)" != "main" ]]; then
    echo "Please be on the main branch when doing a release"
    exit 1
fi

set -e

git pull
git tag "$1"
git push --tags
gh workflow run release.yml --ref "$1"

echo "Release is being created, it will be ready in a couple of minutes."

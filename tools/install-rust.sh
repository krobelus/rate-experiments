#!/bin/sh

set -e

curl https://sh.rustup.rs -sSf > rustup.sh
chmod +x rustup.sh
./rustup.sh -y --default-toolchain 1.36.0
rm rustup.sh

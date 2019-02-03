#!/bin/sh

set -e

curl https://sh.rustup.rs -sSf > rustup.sh
chmod +x rustup.sh
./rustup.sh -y
rm rustup.sh

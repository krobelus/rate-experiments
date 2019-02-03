#!/bin/sh

set -e

host=uranus
repo=rate-experiments

git config remote.$host.url >/dev/null \
    || git remote add $host $host:$repo/.git

cat << EOF | ssh $host
test -d $repo && exit 0
git init $repo
cd $repo
git config receive.denyCurrentBranch updateInstead
EOF

git commit --all --allow-empty --reuse-message HEAD

git push $host master --force-with-lease

for line in \
    "export PATH=~/$repo/tools/bin:\$PATH" \
        'export PATH=~/.cargo/bin/:$PATH' \
        "export LD_LIBRARY_PATH=~/$repo/tools/libevent/.libs:\$LD_LIBRARY_PATH"
do
    ssh $host "grep -Fxq '$line' .profile || echo '$line' >> .profile"
done
cat << EOF | ssh $host
set -e -u
cd $repo
make -C tools
tmux has-session 2>/dev/null || tmux new-session -d

# tmux send-keys C-c
# sleep 0.1
# tmux send-keys './run-all.sh' Enter

EOF

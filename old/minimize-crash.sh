#!/bin/sh


crashes() {
	rate crash.{cnf,drat} 2>&1 | rg -q 'assertion failed: left_position'
}

# while read -p "?" lines_to_delete
test -f crash.cnf.bak && cp crash.cnf.bak crash.cnf
cp crash.cnf crash.cnf.bak

# for i in `seq 1 240`
# do
# 	echo $i
# 	sed ${i}d crash.cnf.bak > crash.cnf
#         crashes && exit 0
# done
# exit 1

while true
do
	test -z "$lines_to_delete" && lines_to_delete=1
	if [ "$lines_to_delete" = s ]; then
        	( sed 1q crash.cnf; sed 1d crash.cnf | shuf ) | sponge crash.cnf
	else
        	( sed 1q crash.cnf; sed 1d crash.cnf | sed 1,${lines_to_delete}d ) | sponge crash.cnf
	fi
	ls -lh crash.cnf
	if crashes; then
                cp crash.cnf crash.cnf.bak
		echo crash
	else
		echo 'no crash'
		# mv crash.cnf.bak crash.cnf
		# shuf < crash.cnf.bak > crash.cnf
        	( sed 1q crash.cnf.bak; sed 1d crash.cnf.bak | shuf ) | sponge crash.cnf
	fi
done

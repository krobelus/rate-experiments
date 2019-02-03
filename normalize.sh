#!/bin/sh

# cp crash.cnf tmp.cnf
# cp crash.drat tmp.drat

edexp=`
(
	sed 1d crash.cnf
	cat crash.drat
) | awk '
{
	for (i=1;i<NF;i++) {
		if ($i !~ /a|d/) {
        		sub("-", "", $i)
        		print $i
		}
	}
}
' | sort -n # | awk '{printf "-e s/%s/%s/g ", $1, NR}'
`
echo $edexp
# sed -i tmp.cnf $edexp
# sed -i tmp.drat $edexp

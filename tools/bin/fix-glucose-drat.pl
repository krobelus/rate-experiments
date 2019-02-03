#!/usr/bin/env perl
die "no such file '$ARGV[0]'" if not -f "$ARGV[0]";
open FILE, "+<", $ARGV[0] or die "error opening '$ARGV[0]'";
seek FILE, -2, 2;
truncate FILE, tell FILE; # remove trailing "0\n"
close FILE;

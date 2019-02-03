#!/usr/bin/env perl
use warnings;
open FILE, $ARGV[0] or die "error opening '$ARGV[0]'";

$comment = 1;
exit 0 if eof FILE;
read FILE, $c, 1; $c = ord($c);
exit 0 if (($c != 13) && ($c != 32) && ($c != 45) && (($c < 48) || ($c > 57))
          && ($c != 99) && ($c != 100));
$comment = 0 if ($c != 99);
exit 0 if eof FILE;
read FILE, $c, 1; $c = ord($c);
exit 0 if (($c != 13) && ($c != 32) && ($c != 45) && (($c < 48) || ($c > 57))
           && ($c != 99) && ($c != 100));
$comment = 0 if ($c != 32);

for ($j = 0; $j < 10; $j++) {
    exit 1 if eof FILE;
    read FILE, $c, 1; $c = ord($c);
    if (($c != 100) && ($c != 10) && ($c != 13) && ($c != 32) &&
        ($c != 45) && (($c < 48) || ($c > 57)) &&
        ($comment && (($c < 65) || ($c > 122)))) {
        exit 0;
    }
}
exit 1;

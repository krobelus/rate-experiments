#!/bin/sh

set -e -u

url="http://sat2018.forsyte.tuwien.ac.at/"

download_archive_name() {
    case "$1" in
        (MapleCOMSPS_LRB_VSIDS_2_fix) echo "${1%_fix}_drup" ;;
        (Maple_LCM_Scavel_200_fix2|Maple_LCM_Scavel_fix2) echo "${1%_fix2}" ;;
        (Riss7.1-fix) echo "${1%-fix}" ;;
        (Sparrow2Riss-2018-fixfix) echo "${1%-fixfix}" ;;
        (*) echo "$1" ;;
    esac
}

fixes() {
    chmod +x varisat/build.sh 2>/dev/null ||:
    chmod +x Lingeling/build/build.sh 2>/dev/null ||:
    chmod +x cms55-main-all4fixed/m4ri-20140914/configure 2>/dev/null ||:
    chmod +x YalSAT/build/build.sh 2>/dev/null ||:
}

solver_with_config="$1"
solver="${solver_with_config%@*}"
config="${solver_with_config#*@}"

echo "@@ $solver"
path=main_and_glucose_hack/"$solver"
zip="../archives/solvers/$solver.zip"
zipurl="$url/solvers/main_and_glucose_hack/$(download_archive_name "$solver").zip"
test -f "$zip" || curl "$zipurl" -o "$zip"
test -d "$solver" || (unzip "$zip" -d "$solver" &&
                        mv "$solver"/* "$solver"/tmp && # glucose-3.0D-patched
                        mv "$solver"/*/* "$solver"
)
fixes
if test -f "$solver"/starexec_build -a ! -f "$solver"/STAREXEC_BUILD_DONE; then
    (cd "$solver" &&
         sh starexec_build < /dev/null \
             || die "build failed for $solver" && touch STAREXEC_BUILD_DONE)
fi

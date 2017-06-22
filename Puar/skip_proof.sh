#!/bin/bash

PLATFORM=`uname`
SED="sed -i"
if [[ "$PLATFORM" == 'Darwin' ]]; then
	SED="$SED .orig"
fi

discard_opts_after_doubledash=0

SHORT=rf:
LONG=remove,file:

# -temporarily store output to be able to check for errors
# -activate advanced mode getopt quoting e.g. via “--options”
# -pass arguments only via   -- "$@"   to separate them correctly
PARSED=$(getopt --options $SHORT --longoptions $LONG --name "$0" -- $@)
if [[ $? -ne 0 ]]; then
    # e.g. $? == 1
    #  then getopt has complained about wrong arguments to stdout
    exit 2
fi
# use eval with "$PARSED" to properly handle the quoting
eval set -- "$PARSED"

file=`ls *.v`

# now enjoy the options in order and nicely split until we see --
while [[ ( ${discard_opts_after_doubledash} -eq 1 ) || ($# -gt 0) ]]; do
    case "$1" in
        -r|--remove)
            r=y
            ;;
        -f|--file)
            file="$2"
            shift
            ;;
        --) if [[ ${discard_opts_after_doubledash} -eq 1 ]]; then break; fi;;
        *)
            echo "$0: Initial Programming error"
            exit 3
            ;;
    esac
    shift
done

# handle non-option arguments
if [[ $# -eq 1 ]]; then
    echo "$0: Final Programming error"
    exit 3
fi

if [ "$r" = y ]; then
	for f in $file;
	do
		echo "Setting SKIP_PROOF_OFF in $f"
		$SED -e 's/(\* SKIP_PROOF_ON/(\* SKIP_PROOF_OFF \*)/g' \
			-e 's/END_SKIP_PROOF_ON \*) apply cheat\./(\* END_SKIP_PROOF_OFF \*)/g' "$f"
	done
else
	for f in $file
	do
		echo "Setting SKIP_PROOF_ON in $f"
		#grep "SKIP_PROOF" "$f" > /dev/null &&
		$SED -e 's/(\* SKIP_PROOF_OFF \*)/(\* SKIP_PROOF_ON/g' \
			-e 's/(\* END_SKIP_PROOF_OFF \*)/END_SKIP_PROOF_ON \*) apply cheat\./g' "$f"
	done
fi

rm -f */*.orig

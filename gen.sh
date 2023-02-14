#!/bin/bash

# Generate SMT benchmarks from a TLA+ specification
# Usage: ./gen.sh Spec.tla args.conf path_to_tlapm_dir path_to_community_modules_dir

spec_file=$1
conf_file=$2
tlapm_dir=$3
community_modules=$4


tlapm=tlapm
benchs=benchs
cachedir=.tlacache

specdir=$(dirname $spec_file)
specpath=$(echo $spec_file | cut -d'/' -f2-)
specname=$(basename -s .tla $spec_file)
confname=$(basename -s .conf $conf_file)

exec 3< $conf_file
read -u 3 suffix
read -u 3 flags
read -u 3 meth
read -u 3 smt_logic


tlapsdir=$cachedir/$specname.tlaps
benchdir=$benchs/$(dirname $specpath)/$specname/$confname

# Check for existing .tlaps dir
if [ -d $tlapsdir ]; then
    rm -f $tlapsdir/*.$suffix
fi

# Check for existing problem files
mkdir -p $benchdir
if [ -n "$(find $benchdir -name *.$suffix)" ]; then
    echo ".$suffix files found in '$benchdir' dir"
    echo "Please run:"
    echo "rm $benchdir/*.$suffix"
    exit
fi

# Run TLAPS

echo -e "Running TLAPS on specification \e[1m$spec_file\e[0m with configuration \e[1m$conf_file\e[0m"

cmd="$tlapm --cache-dir $cachedir -I $tlapm_dir -I $community_modules -I $specdir --toolbox 0 0 --nofp --stretch 0.5 --debug tempfiles --smt-logic $smt_logic --method $meth --debug $flags $spec_file"

# This spec in particular needs an additional include
if [ $spec_file = "tla_specs/Original/TLAplus_Examples/specifications/ewd998/AsyncTerminationDetection_proof.tla" ]; then
    cmd="$cmd -I tla_specs/Original/TLAplus_Examples/specifications/ewd840/"
fi

echo "$cmd"
eval "$cmd > /dev/null 2>&1"

# Moving benchmarks and Cleaning .tlaps dir
mv -t $benchdir $tlapsdir/*.$suffix
rm -rf $tlapsdir

echo 'Done'


#! /bin/bash

z3_versions=(
    "4.10.1"
    "4.11.2"
    "4.12.1"
    "4.12.2"
    "4.4.2"
    "4.5.0"
    "4.6.0"
    "4.8.11"
    "4.8.17"
    "4.8.5"
    "4.8.6"
    "4.8.7"
    "4.8.8"
)

for z3_version in "${z3_versions[@]}"; do

    echo "obtaining z3 $z3_version"

    if [ `uname` == "Darwin" ]; then
        if [[ $(uname -m) == 'arm64' ]]; then
            filename=z3-$z3_version-arm64-osx-11.0
        else
            filename=z3-$z3_version-x64-osx-10.16
        fi
    elif [ `uname` == "Linux" ]; then
        filename=z3-$z3_version-x64-glibc-2.31
    fi
    
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
    if [ $? -ne 0 ]; then
        echo "z3 $z3_version is not available for $(uname) $(uname -m)"
    else
        unzip -q $filename.zip
        
        # delete the existing z3 because of caching issue on macs
        rm -f solvers/z3-$z3_version
        
        cp $filename/bin/z3 solvers/z3-$z3_version
        rm -r $filename
        rm $filename.zip
    fi

done

cvc5_versions=(
    "1.0.3"
)

for cvc5_version in "${cvc5_versions[@]}"; do

    if [ `uname` == "Darwin" ]; then
        if [[ $(uname -m) == 'arm64' ]]; then
            filename=cvc5-macOS-arm64
        else
            filename=cvc5-macOS
        fi
    elif [ `uname` == "Linux" ]; then
        filename=cvc5-Linux
    fi

    wget -q https://github.com/cvc5/cvc5/releases/download/cvc5-$cvc5_version/$filename

    if [ $? -ne 0 ]; then
        echo "cvc5 $cvc5_version is not available for $(uname) $(uname -m)"
    else
        # delete the existing cvc5 because of caching issue on macs
        rm -f solvers/cvc5-$cvc5_version
        cp $filename solvers/cvc5-$cvc5_version
        chmod +x solvers/cvc5-$cvc5_version
        rm $filename
    fi
done

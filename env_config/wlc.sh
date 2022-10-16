#!/bin/sh
mkdir relic-tmp && cd relic-tmp 
cmake .. -DCHECK=off -DARITH=gmp -DFP_PRIME=256 -DEP_PRECO=ON -DEP_PLAIN=ON -DFP_METHD="INTEG;COMBA;COMBA;MONTY;MONTY;LOWER;SLIDE" -DCFLAGS="-O3 -funroll-loops -fomit-frame-pointer -march=native -mtune=native" $1
make -j8
sudo make install
sudo ldconfig
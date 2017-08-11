#!/bin/sh

rm -f output/*.out
for i in *.julia; do ./juliaTest.native "$i" 2> output/$i.out;  done


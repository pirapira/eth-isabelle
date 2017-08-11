#!/bin/sh

rm -f test_output/*.out
for i in *.julia; do ./juliaTest.native "$i" 2> test_output/$i.out;  done


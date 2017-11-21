#!/bin/sh

for i in *.julia; do
  ./juliaTest.native "$i" 2> test_output/$i.out2;
  cmp --silent test_output/$i.out test_output/$i.out2 || ( echo "they were different" ; exit 1 )
done


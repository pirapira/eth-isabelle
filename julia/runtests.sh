#!/bin/sh

for i in *.julia; do
  ./juliaTest.native "$i" 2> output/$i.out2;
  cmp --silent output/$i.out output/$i.out2 || ( echo "they were different" ; exit 1 )
done


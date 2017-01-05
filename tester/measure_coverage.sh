rm -f bisect* || { echo "should not happen"; exit 1; }
sh compile.sh || { echo 'compilation failed.'; exit 1; }
./runVmTest.native || { echo 'VMTest failed.'; exit 1; }
cd _build
bisect-ppx-report -I build/ -html ../coverage/ ../bisect*.out
echo "Open coverage/index.html"



(*
   Copyright 2016 Yoichi Hirai

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

theory FeeSchedule

imports Main "~~/src/HOL/Word/Word"

begin

text "Appendix G. Fee Schedule"

text "What type is a fee?"
text "Maybe uint256.  Maybe nat."
text "There would be calculations with huge numbers.  Then nat would be too slow."
text "But, I will be doing mathematical induction on these values nat."

definition "Gstep = (1 :: nat)"
definition "Gbalance = (20 :: nat)"
definition "Gstop = (0 :: nat)"
definition "Gsuicide = (0 :: nat)"
definition "Gsload = (20 :: nat)"
definition "Gzero = (0 :: nat)"
definition "Gbase = (2 :: nat)"
definition "Gverylow = (3 :: nat)"
definition "Glow = (5 :: nat)"
definition "Gmid = (8 :: nat)"
definition "Ghigh = (10 :: nat)"
definition "Gext = (20 :: nat)"
definition "Gjumpdest = (1 :: nat)"
definition "Gsset = (20000 :: nat)"
definition "Gsreset = (5000 :: nat)"
definition "Rsclear = (15000 :: nat)"
definition "Rsuicide = (24000 :: nat)"
definition "Gcreate = (32000 :: nat)"
definition "Gcodedeposit = (200 :: nat)"
definition "Gcall = (40 :: nat)"
definition "Gcallvalue = (9000 :: nat)"
definition "Gcallstipend = (2300 :: nat)"
definition "Gcallnewaccount = (25000 :: nat)"
definition "Gexp = (10 :: nat)"
definition "Gexpbyte = (10 :: nat)"
definition "Gmemory = (3 :: nat)"
definition "Gtxdatazero = (4 :: nat)"
definition "Gtxdatanonzero = (68 :: nat)"
definition "Gtransaction = (21000 :: nat)"
definition "Glog = (375 :: nat)"
definition "Glogdata = (8 :: nat)"
definition "Glogtopic = (375 :: nat)"
definition "Gsha3 = (30 :: nat)"
definition "Gsha3word = (6 :: nat)"
definition "Gcopy = (3 :: nat)"

end

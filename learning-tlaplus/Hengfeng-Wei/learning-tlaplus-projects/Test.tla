-------------------------------- MODULE Test --------------------------------
EXTENDS Naturals

One == 1

Six == LET Two == 2 
        IN LET Three == 3
            IN One + Two + Three
=============================================================================
\* Modification History
\* Last modified Mon Sep 03 20:02:18 CST 2018 by hengxin
\* Created Mon Sep 03 20:00:20 CST 2018 by hengxin

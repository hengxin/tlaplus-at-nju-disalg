------------------------ MODULE AJupiterFixedInputMC ------------------------
EXTENDS AJupiter

CONSTANTS   
    Cop         \* Cop[c]: operations issued by the client c \in Client
    
AJupiterSystem == INSTANCE AJupiter 

ASSUME 
    /\ Cop \in [Client -> Seq(Op)]
    
=============================================================================
\* Modification History
\* Last modified Thu Jul 26 06:23:14 CST 2018 by hengxin
\* Created Sun Jul 15 15:25:43 CST 2018 by hengxin

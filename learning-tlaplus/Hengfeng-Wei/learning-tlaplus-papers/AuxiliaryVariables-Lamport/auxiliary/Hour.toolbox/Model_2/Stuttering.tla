----------------------------- MODULE Stuttering ----------------------------
(***************************************************************************)
(* A module that provides operators used to add stuttering variables to    *)
(* specifications.  See the paper "Prophecy Variables Made Simple"(?) by   *)
(* Lamport and Merz.  To give the stuttering variable another name, the    *)
(* module must be instantiated.                                            *)
(*                                                                         *)
(* The constant top should be chosen to be a value that isn't a record     *)
(* with `type', `name', and `val' fields.  For model checking, it should   *)
(* be set to a model value.                                                *)
(***************************************************************************)
EXTENDS Naturals, TLC
top == [top |-> "top"] 

VARIABLES s, vars

NoStutter(A) == (s = top) /\ A /\ (s' = s)

PostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ UNCHANGED vars 
                  /\ s'= IF s.val = bot THEN top 
                                        ELSE [s EXCEPT !.val = decr(s.val)]

PreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ UNCHANGED vars 
         /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal] 
    ELSE /\ s.id = actionId 
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)]
-----------------------------------------------------------------------------                                 
MayPostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = IF initVal = bot
                            THEN s
                            ELSE [id |-> actionId, ctxt |-> context, 
                                  val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ UNCHANGED vars 
                  /\ s'= IF decr(s.val) = bot 
                           THEN top 
                           ELSE [s EXCEPT !.val = decr(s.val)]

MayPreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ UNCHANGED vars 
         /\ IF initVal = bot
              THEN A /\ (s' = s)
              ELSE s' = [id |-> actionId, ctxt |-> context, val |-> initVal] 
    ELSE /\ s.id = actionId 
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)] 
-----------------------------------------------------------------------------
StutterConstantCondition(Sigma, bot, decr(_)) ==
  LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
      R[n \in Nat] == IF n = 0 THEN {bot}
                               ELSE LET T == R[n-1] 
                                    IN  T \cup InverseDecr(T)
                        
  IN Sigma = UNION {R[n] : n \in Nat}
\*   LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
\*       ReachBot[S \in SUBSET Sigma] ==
\*          IF InverseDecr(S) = {} THEN S 
\*                                 ELSE ReachBot[S \cup InverseDecr(S)]
\*   IN  ReachBot[{bot}] = Sigma


=============================================================================
\* Modification History
\* Last modified Mon Oct 17 04:13:47 PDT 2016 by lamport
\* Created Tue Dec 08 11:51:34 PST 2015 by lamport

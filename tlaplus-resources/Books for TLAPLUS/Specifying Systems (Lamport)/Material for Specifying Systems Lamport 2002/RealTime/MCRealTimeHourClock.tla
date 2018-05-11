
------------------------- MODULE MCRealTimeHourClock --------------------------
EXTENDS Naturals, HourClock 
VARIABLE now 
CONSTANT Rho, MaxReal, SecondsPerHour
Real == 0 .. MaxReal
ASSUME (Rho \in Real) /\  (Rho > 0) 
-----------------------------------------------------------------------------
   VARIABLE t  
   TNext == t' = IF HCnxt THEN 0 ELSE t+(now'-now) 
   IsTimer == (t = 0)  /\  [][TNext]_<<t,hr,now>>
   MaxTime == [](t \leq  SecondsPerHour + Rho)  
   MinTime == [][HCnxt => t \geq SecondsPerHour - Rho]_hr
   HCTime == IsTimer /\ MaxTime /\ MinTime 

NowNext == /\ now' \in {r \in Real : r > now} 
           /\ UNCHANGED hr  

BigNext == /\ [NowNext]_now
           /\ [HCnxt]_hr
           /\ TNext
           /\ HCnxt => t \geq SecondsPerHour - Rho
           /\ t' \leq  SecondsPerHour + Rho

BigInit == /\ HCini
           /\ t = 0
           /\ now \in Real 

Fairness == \A r \in Real : WF_now(NowNext /\ (now'>r))

BigSpec == BigInit /\ [][BigNext]_<<now, hr, t>> /\ Fairness

NonZeno == \A r \in Real : <>(now \geq r)

ImpliedTemporal == \A h \in 1..12 : []<>(hr = h)

Constraint == now \in 0 .. (MaxReal-1)
  (*************************************************************************)
  (* Need to constrain `now' in this way, otherwise specification is       *)
  (* violated by a behavior that remains forever with now=MaxReal, since   *)
  (* NowNext /\ (now'>r) is not enabled in such a state, so the Fairness   *)
  (* condition does not rule out this behavior.                            *)
  (*************************************************************************)
  
RT == /\ now \in Real 
      /\ [][NowNext]_now
      /\ \A r \in Real : WF_now(NowNext /\ (now'>r))
=============================================================================
 
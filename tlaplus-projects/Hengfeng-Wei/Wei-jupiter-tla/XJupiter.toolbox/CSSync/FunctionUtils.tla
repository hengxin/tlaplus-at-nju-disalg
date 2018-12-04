-------------------- MODULE FunctionUtils --------------------
(***************************************************************************)
(* Additional Operations for Functions.                                    *)
(***************************************************************************)
Range(f) == {f[a] : a \in DOMAIN f}

Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])

Surjective(f, B) == \A b \in B: \E a \in DOMAIN f: f[a] = b 
=============================================================================
\* Modification History
\* Last modified Mon Dec 03 20:14:46 CST 2018 by hengxin
\* Created Tue Aug 28 10:35:49 CST 2018 by hengxin
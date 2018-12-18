--------------------------- MODULE FunctionUtils ---------------------------
Range(f) == {f[a] : a \in DOMAIN f}

Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])

Surjective(f, B) == \A b \in B: \E a \in DOMAIN f: f[a] = b 

=============================================================================
\* Modification History
\* Last modified Wed Dec 12 20:34:35 CST 2018 by jywellin
\* Created Wed Dec 12 20:34:15 CST 2018 by jywellin

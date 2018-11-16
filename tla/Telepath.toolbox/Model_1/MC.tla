---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_15423012222426000 == 
{c1, c2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15423012222427000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15423012222428000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Thu Nov 15 12:00:22 EST 2018 by john

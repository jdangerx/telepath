---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239190841642000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239190841743000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239190841744000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239190841745000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:11:48 EST 2018 by dsherry

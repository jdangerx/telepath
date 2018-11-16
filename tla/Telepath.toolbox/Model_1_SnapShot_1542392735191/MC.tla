---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239272714578000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239272714579000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239272714580000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239272714581000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:25:27 EST 2018 by dsherry

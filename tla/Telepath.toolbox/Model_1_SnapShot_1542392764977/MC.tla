---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239275793587000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239275793588000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239275793589000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239275793590000 ==
TypeInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154239275793591000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:25:57 EST 2018 by dsherry

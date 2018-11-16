---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239300783897000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239300783898000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239300783899000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1542393007838100000 ==
TypeInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1542393007838101000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:30:07 EST 2018 by dsherry

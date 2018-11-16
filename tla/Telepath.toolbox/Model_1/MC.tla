---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_1542394649291102000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_1542394649291103000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1542394649291104000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1542394649291105000 ==
TypeInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1542394649291106000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:57:29 EST 2018 by dsherry

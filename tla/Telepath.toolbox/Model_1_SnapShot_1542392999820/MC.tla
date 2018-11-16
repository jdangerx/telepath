---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239299277792000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239299277793000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239299277794000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239299277795000 ==
TypeInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154239299277796000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:29:52 EST 2018 by dsherry

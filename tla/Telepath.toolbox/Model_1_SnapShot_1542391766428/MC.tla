---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239175838538000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239175838539000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239175838540000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239175838541000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:09:18 EST 2018 by dsherry

---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Clients
const_154239267006861000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:3MaxMessageLength
const_154239267006962000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154239267006963000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154239267006964000 ==
TypeInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154239267006965000 ==
EventualConsistency
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 13:24:30 EST 2018 by dsherry

import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros

-- Generic searches (not RS-specific)—sanity-check presence in Mathlib
#find _ ≤ _
#find IsOpen (Metric.ball ?_ ?_)
#find IsPreconnected (Metric.ball ?_ ?_)
#find AnalyticAt ?f ?z
#find AnalyticOn ?f ?s
#find Filter.Tendsto ?f ?l ?l'

import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Data.Real.Basic
import banach_tarski.Lemma_3_1

def L := {x: r_3 | x ∈ Metric.ball 0 1}
def origin : r_3 := ![0,0,0]
def L' := L \ {origin}

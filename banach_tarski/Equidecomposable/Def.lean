import Mathlib.Data.List.Basic

import banach_tarski.Definitions

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Partition.Finpartition

import Mathlib.Analysis.NormedSpace.AffineIsometry

import banach_tarski.Lemma_3_1

import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Analysis.NormedSpace.Basic

universe u v
variable (α : Type u) [NormedField α] (n : Type v) [SeminormedAddCommGroup n]

abbrev s := NormedSpace α n

def equidecomposable (X Y : Set s) : Prop :=
  ∃ Parts_X : Finpartition X, ∃ Parts_Y : Finpartition Y, ∃ transformations : {w : List (AffineIsometry β) // w.length = Parts_X.parts.card},
  true

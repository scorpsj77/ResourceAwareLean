/-
Copyright (c) 2026 Lechen Wang, Daya Kumaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lechen Wang, Daya Kumaran
-/
import ResourceAware.Foundations.Graph.Interface
import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Representation-independent weighted shortest paths

This module turns the edge occurrences of a `WeightedEdgeView` into a quiver. Paths retain the
identity and weight of every traversed occurrence, so parallel edges remain distinguishable.
The definitions are independent of Dijkstra's algorithm and of any concrete graph representation.
-/

namespace ResourceAware.Algorithms.ShortestPaths

open ResourceAware.Graph

universe u v w x

/-- A weighted edge occurrence between fixed endpoints in a selected graph. -/
structure WeightedArc {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight) (g : G)
    (source target : V) where
  edge : Edge
  weight : Weight
  valid : Ω.Arc g edge source target weight

/-- The weighted edge occurrences form the arrows of a quiver. -/
@[reducible]
def weightedArcQuiver {G : Type u} {V : Type v} {Edge : Type w}
    {Weight : Type x} {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight)
    (g : G) : Quiver V where
  Hom := WeightedArc Ω g

/-- A directed path whose arrows retain exact weighted edge occurrences. -/
abbrev NetworkPath {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight) (g : G)
    (source target : V) :=
  @Quiver.Path V (weightedArcQuiver Ω g) source target

/-- Sum the selected occurrence weights along a network path. -/
def pathWeight {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight) (g : G)
    [AddMonoid Weight] {source target : V} (path : NetworkPath Ω g source target) :
    Weight :=
  letI := weightedArcQuiver Ω g
  Quiver.Path.addWeight (fun arc : WeightedArc Ω g _ _ => arc.weight) path

/-- A path is shortest when no path with the same endpoints has smaller additive weight. -/
def IsShortestPath {G : Type u} {V : Type v} {Edge : Type w} {Weight : Type x}
    {Γ : Interface G V} (Ω : WeightedEdgeView Γ Edge Weight) (g : G)
    [AddMonoid Weight] [LE Weight] {source target : V}
    (path : NetworkPath Ω g source target) : Prop :=
  ∀ alternative : NetworkPath Ω g source target,
    pathWeight Ω g path ≤ pathWeight Ω g alternative

end ResourceAware.Algorithms.ShortestPaths

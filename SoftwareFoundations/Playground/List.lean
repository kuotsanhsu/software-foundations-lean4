
#check Acc
#check WellFounded
class PreLegacyForwardIterator.{u,v} (It: Type u) where
  [decEq: DecidableEq It]
  reference: Type v
  last: It
  get it: it ≠ last → reference
  next it: it ≠ last → It

namespace PreLegacyForwardIterator
  universe u
  variable {It: Type u} [PreLegacyForwardIterator It]
  
  inductive ReachLast: It → Prop
    | last: ReachLast last
    | back {it} (h: it ≠ last): ReachLast (next it h) → ReachLast it

  inductive le: It → It → Prop
    | last {it}: le it last
    | back {it it'} (h: it ≠ last): le (next it h) it' → le it it'

  instance: LE It where
    le := le
end PreLegacyForwardIterator

class LegacyForwardIterator.{u} (It: Type u) extends
  PreLegacyForwardIterator It where
  reachLast (it: It): toPreLegacyForwardIterator.ReachLast it

namespace LegacyForwardIterator
  universe u
  variable {It: Type u} [LegacyForwardIterator It]
  
  instance decLE (it it': It): Decidable (it ≤ it') := sorry

  def distance (first last: It): first ≤ last → Nat := sorry
  --   | .last it => _
  --   | .back hn h => _
end LegacyForwardIterator

class PreContainer.{u,v} (C: Type u) where
  const_iterator: Type v
  [legacyForwardIterator: LegacyForwardIterator const_iterator]
  cbegin: C → const_iterator

namespace PreContainer
  universe u v
  variable {C: Type u} [self: PreContainer C] (c: C)

  def cend: self.const_iterator := legacyForwardIterator.last
  def empty: Prop := cbegin c = cend
  instance: Decidable (empty c) := legacyForwardIterator.decEq _ _
end PreContainer

class Container.{u} (C: Type u) extends PreContainer C where
  [decEq: DecidableEq C]
  new: C
  new_empty: toPreContainer.empty new
  size: C → Nat
  size_distance (c: C)
    : size c =
      legacyForwardIterator.distance (cbegin c) toPreContainer.cend .last

namespace Container
  universe u v w
  variable {C: Type w} [Container C]
end Container

instance {T} [DecidableEq T]: LegacyForwardIterator (List T) where
  reference := T
  last := []
  get  | head::_, _ => head
  next | _::tail, _ => tail

instance {T} [DecidableEq T]: Container (List T) where
  new := []
  new_empty := rfl
  cbegin := id
  size := List.length
  size_distance := sorry


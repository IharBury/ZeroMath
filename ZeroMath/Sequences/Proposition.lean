import ZeroMath.Sequences.Progression

namespace ZeroMath.Sequences

namespace Proposition

/-- The length of a finite progression witnessed by `index`, a positive ordinal
at which `Progression.tryGetElement` returns `none`. Counts the number of
elements before the first `none`. -/
def getLength {α : Type u} (p : Progression α)
    (index : Numbers.OrdinalNatural.Peano)
    (_h : Progression.tryGetElement index p = none) :
    Numbers.CardinalNatural.Peano :=
  let rec aux : Option α → Numbers.CardinalNatural.Peano → Numbers.CardinalNatural.Peano
    | none, _ => Numbers.CardinalNatural.Peano.zero
    | some _, Numbers.CardinalNatural.Peano.zero =>
        Numbers.CardinalNatural.Peano.zero
    | some x, Numbers.CardinalNatural.Peano.successor fuel =>
        Numbers.CardinalNatural.Peano.successor (aux (p.next x) fuel)
  aux p.first (Numbers.CardinalNatural.Peano.fromOrdinal index)

end Proposition

end ZeroMath.Sequences

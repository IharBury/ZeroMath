import ZeroMath.Sequences.Progression

namespace ZeroMath.Sequences

namespace Proposition

/-- The length of a finite progression: the number of elements before
`Progression.tryGetElement` first returns `none`. -/
noncomputable def getLength {α : Type u} (p : Progression α)
    (h : Progression.Finite p) : Numbers.CardinalNatural.Peano :=
  let rec aux : Option α → Numbers.CardinalNatural.Peano → Numbers.CardinalNatural.Peano
    | none, _ => Numbers.CardinalNatural.Peano.zero
    | some _, Numbers.CardinalNatural.Peano.zero =>
        Numbers.CardinalNatural.Peano.zero
    | some x, Numbers.CardinalNatural.Peano.successor fuel =>
        Numbers.CardinalNatural.Peano.successor (aux (p.next x) fuel)
  aux p.first (Numbers.CardinalNatural.Peano.fromOrdinal (Classical.choose h))

end Proposition

end ZeroMath.Sequences

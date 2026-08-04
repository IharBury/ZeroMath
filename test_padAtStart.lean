import ZeroMath.Sequences.List

namespace ZeroMath.Sequences
namespace List

open ZeroMath.Numbers.CardinalNatural

example {α : Type} (l : List α) (p : α) :
    padAtStart l p Peano.zero = l := rfl

example {α : Type} (l : List α) (p : α) :
    padAtStart l p (Peano.successor Peano.zero) = firstElement p l := rfl

example {α : Type} (l : List α) (p : α) :
    padAtStart l p (Peano.successor (Peano.successor Peano.zero)) = firstElement p (firstElement p l) := rfl

end List
end ZeroMath.Sequences

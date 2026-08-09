import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Numbers.Digits

/-- A base-10 digit: a cardinal Peano natural strictly less than ten. -/
def Decimal := { d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten }

deriving instance DecidableEq for Decimal

def zeroDigit : Decimal := ⟨CardinalNatural.Peano.zero, by decide⟩
def oneDigit : Decimal := ⟨CardinalNatural.Peano.one, by decide⟩
def twoDigit : Decimal := ⟨CardinalNatural.Peano.two, by decide⟩
def threeDigit : Decimal := ⟨CardinalNatural.Peano.three, by decide⟩
def fourDigit : Decimal := ⟨CardinalNatural.Peano.four, by decide⟩
def fiveDigit : Decimal := ⟨CardinalNatural.Peano.five, by decide⟩
def sixDigit : Decimal := ⟨CardinalNatural.Peano.six, by decide⟩
def sevenDigit : Decimal := ⟨CardinalNatural.Peano.seven, by decide⟩
def eightDigit : Decimal := ⟨CardinalNatural.Peano.eight, by decide⟩
def nineDigit : Decimal := ⟨CardinalNatural.Peano.nine, by decide⟩

end ZeroMath.Numbers.Digits

namespace ZeroMath.Logic

inductive Dichotomy (P Q : Prop) : Prop where
  | first (p : P) (nq : ¬Q) : Dichotomy P Q
  | second (q : Q) (np : ¬P) : Dichotomy P Q

end ZeroMath.Logic

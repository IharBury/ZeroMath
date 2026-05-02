namespace ZeroMath.Logic

inductive Trichotomy (P Q R : Prop) : Prop where
  | first (p : P) (nq : ¬Q) (nr : ¬R) : Trichotomy P Q R
  | second (q : Q) (np : ¬P) (nr : ¬R) : Trichotomy P Q R
  | third (r : R) (np : ¬P) (nq : ¬Q) : Trichotomy P Q R

end ZeroMath.Logic

namespace ZeroMath.Logic

inductive Trichotomy (P Q R : Prop) : Prop where
  | left (p : P) (nq : ¬Q) (nr : ¬R) : Trichotomy P Q R
  | center (q : Q) (np : ¬P) (nr : ¬R) : Trichotomy P Q R
  | right (r : R) (np : ¬P) (nq : ¬Q) : Trichotomy P Q R

end ZeroMath.Logic

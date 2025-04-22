import Data.List

%default total

data Formula = Atom Type | Top | Bot | And Formula Formula |
               Or Formula Formula | Implies Formula Formula

infixl 5 &&
infixl 4 ||
infixr 3 =.>

(&&) : Formula -> Formula -> Formula
(&&) x y = And x y

(||) : Formula -> Formula -> Formula
(||) x y = Or x y

(=.>) : Formula -> Formula -> Formula
(=.>) x y = Implies x y

¬ : Formula -> Formula
¬ x = x =.> Bot

data Contains : {a : Type} -> List a -> (x : a) -> Type where
  First : Contains (a::as) a
  Nth   : Contains xs x -> Contains (y::xs) x

discharge : (fs : List Formula) -> (f : Formula) -> Contains fs f -> List Formula
discharge (_ :: as) f First = as
discharge (y :: xs) f (Nth prf) = y :: (discharge xs f prf)

data Derivation : List Formula -> Formula -> Type where
  Assume : (xs : List Formula) -> {auto prf : NonEmpty xs} -> Derivation xs (head xs)

  Cont   : (f : Formula) -> Derivation xs g -> {auto prf : Contains xs f} -> {auto _ : Contains (discharge xs f prf) f} -> Derivation (discharge xs f prf) g

  AndI   : Derivation xs f -> Derivation ys g -> Derivation (xs ++ ys) (f && g)
  AndEL  : Derivation xs (f && g) -> Derivation xs f
  AndER  : Derivation xs (f && g) -> Derivation xs g

  NegI   : (f : Formula) -> Derivation xs Bot -> {auto prf : Contains xs f} -> Derivation (discharge xs f prf) (¬ f)

  OrIL   : (f : Formula) -> Derivation xs g -> Derivation xs (f || g)
  OrIR   : (f : Formula) -> Derivation xs g -> Derivation xs (g || f)
  OrE    : Derivation xs (f =.> h) -> Derivation ys (g =.> h) -> Derivation zs (f || g) -> Derivation (xs ++ ys ++ zs) h

  ImpI   : (f : Formula) -> Derivation xs g -> {auto prf : Contains xs f} -> Derivation (discharge xs f prf) (f =.> g)
  ImpE   : Derivation xs (a =.> b) -> Derivation ys a -> Derivation (xs ++ ys) b

  EFQ    : (f : Formula) -> Derivation xs Bot -> Derivation xs f

infixl 5 |-

(|-) : List Formula -> Formula -> Type
(|-) = Derivation

MP : {a, b : Formula} -> [] |- (a =.> b) -> [] |- a -> [] |- b
MP = ImpE

int1 : {a, b : Formula} -> [] |- (a =.> b =.> a)
int1 = ImpI a $
      ImpI b $
      Assume (a::[b])

int2 : {a, b, c : Formula} -> [] |- ((a =.> b =.> c) =.> ((a =.> b) =.> (a =.> c)))
int2 = ImpI (a =.> (b =.> c)) $
      ImpI (a =.> b) $
      ImpI a $
      Cont a $
      ImpE (
        ImpE (
          Assume [a =.> b =.> c]
        ) (
          Assume [a]
        )
      ) (
        ImpE (
          Assume [a =.> b]
        ) (
          Assume [a]
        )
      )

int3 : {a, b : Formula} -> [] |- (a && b =.> a)
int3 = ImpI (a && b) $
      AndEL $
      Assume ((a && b)::Nil)

int4 : {a, b : Formula} -> [] |- (a && b =.> b)
int4 = ImpI (a && b) $
      AndER $
      Assume $ ((a && b)::Nil)

int5 : {a, b : Formula} -> [] |- (a =.> a || b)
int5 = ImpI a $ OrIR b $ Assume [a]

int6 : {a, b : Formula} -> [] |- (b =.> a || b)
int6 = ImpI b $ OrIL a $ Assume [b]

int7 : {a, b, c : Formula} -> [] |- ((a =.> b) =.> ((c =.> b) =.> (a || c =.> b)))
int7 = ImpI (a =.> b) $
      ImpI (c =.> b) $
      ImpI (a || c) $
      OrE (
        Assume [a =.> b]
      ) (
        Assume [c =.> b]
      ) (
        Assume [a || c]
      )

int8 : {a : Formula} -> [] |- (Bot =.> a)
int8 = ImpI Bot $ EFQ a $ Assume [Bot]

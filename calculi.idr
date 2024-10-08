import Data.List

%default total

data Formula : Type where
  Atom  : Type -> Formula
  And   : Formula -> Formula -> Formula
  Or    : Formula -> Formula -> Formula
  Not   : Formula -> Formula
  If    : Formula -> Formula -> Formula
  Top   : Formula
  Bot   : Formula

¬ : Formula -> Formula
¬ x = Not x

→ : Formula -> Formula -> Formula
→ x y = If x y

∧ : Formula -> Formula -> Formula
∧ x y = And x y

shiftN : Nat -> (l : List a) -> {auto prf : NonEmpty l} -> List a
shiftN _ [] impossible
shiftN 0 b@(x :: xs) = b
shiftN (S n) b@(x :: []) = [x]
shiftN (S n) b@(x :: (y::ys)) = y :: (shiftN n (x::ys))

simpleShiftN : shiftN 3 [0, 1, 2, 3] = [1, 2, 3, 0]
simpleShiftN = Refl

headNth : Nat -> (l : List a) -> List a
headNth = \n => headNthHelp n n
  where
    headNthHelp : Nat -> Nat -> (l : List a) -> List a
    headNthHelp k 0 l = l
    headNthHelp k (S j) [] = []
    headNthHelp k (S j) (x :: xs) = headNthHelp k j (shiftN k (x::xs))

simpleHeadNth : headNth 3 [0, 1, 2, 3, 4, 5] = [3, 0, 1, 2, 4, 5]
simpleHeadNth = Refl

data Derivation : List Formula -> Formula -> Type where
  Empty : Derivation [] Top

  HeadAsmp : (n : Nat) -> Derivation as f -> Derivation (headNth n as) f

  NegI : Derivation (f::as) Bot -> Derivation as (Not f)
  NegE : Derivation as f -> Derivation bs (Not f) -> Derivation (as ++ bs) Bot

  AndEL : Derivation as (And f g) -> Derivation as f
  AndER : Derivation as (And f g) -> Derivation as g
  AndI  : Derivation as f -> Derivation bs g -> Derivation (as ++ bs) (And f g)

  OrE  : Derivation (f::bs) h -> Derivation (g::cs) h -> Derivation as (Or f g) -> Derivation (as ++ bs ++ cs) h
  OrIL : Derivation as f -> (g : Formula) -> Derivation as (Or g f)
  OrIR : Derivation as f -> (g : Formula) -> Derivation as (Or f g)

  ImpE : Derivation as (If f g) -> Derivation bs f -> Derivation (as ++ bs) g
  ImpI : Derivation (f :: as) g -> Derivation as (If f g)

  -- structural rules
  THIN : Derivation as f -> Derivation bs g -> Derivation as f
  Assume : (g : Formula) -> Derivation as f -> Derivation (g :: as) g

  -- intuitionistic rules
  EFQ : (f : Formula) -> Derivation as Bot -> Derivation as f

  -- 'classical' rules
  TND : (a : Formula) -> (b : Formula) -> Derivation [] (Or a b)
  CR  : Derivation ((Not p)::as) Bot -> Derivation as p

data Step : List Formula -> (f : Formula) -> (g : Formula) -> Type where
  Start     : Step [] Top Top
  OneRule   : Step xs a b -> (Derivation xs b -> Derivation ys c) -> Step ys a c
  TwoRule   : (Derivation xs b -> Derivation ys c -> Derivation zs d) -> (Step xs a b, Step ys a c) -> Step zs a d
  ThreeRule : (Derivation xs b -> Derivation ys c -> Derivation zs d -> Derivation us e) -> (Step xs a b, Step ys a c, Step zs a d) -> Step us a e

(~~) : Step xs a b -> (step : Derivation xs b -> Derivation ys c) -> Step ys a c
(~~) = OneRule

(~~~) : (Derivation xs b -> Derivation ys c -> Derivation zs d) -> (Step xs a b, Step ys a c) -> Step zs a d
(~~~) = TwoRule

(~~~~) : (step : Derivation xs b -> Derivation ys c -> Derivation zs d -> Derivation us e) -> (Step xs a b, Step ys a c, Step zs a d) -> Step us a e
(~~~~) = ThreeRule

infixl 5 ~~
infixl 5 ~~~

⊢ : List Formula -> Formula -> Type
⊢ fs f = Step fs Top f

th1 : {a, b : Formula} -> [] `⊢` (((a `∧` b) `→` a) `∧` ((a `∧` b) `→` b))
th1 = AndI ~~~ (left, right)
  where
    left : [] `⊢` ((a `∧` b) `→` a)
    left = Start
      ~~(Assume((a `∧` b)))
      ~~(AndEL)
      ~~(ImpI)

    right : [] `⊢` ((a `∧` b) `→` b)
    right = Start
      ~~(Assume((a `∧` b)))
      ~~(AndER)
      ~~(ImpI)

ex1 : {p : Formula} -> [p] `⊢` (¬(¬ p))
ex1 = NegE ~~~ (left, right)
  -- Bot, [p, ¬ p]
  ~~ (HeadAsmp 1)
  -- Bot, [¬ p, p]
  ~~ NegI
  -- ¬(¬ p), [p]
  where
    left : [p] `⊢` p
    left = Start
      ~~(Assume p)

    right : [¬ p] `⊢` ¬ p
    right = Start
      ~~(Assume $ ¬ p)

-- there should also be an intuitionistic proof of this...
ex2 : {p : Formula} -> [¬ (¬ (¬ p))] `⊢` (¬ p)
ex2 = NegE ~~~ (left, right) ~~ CR
  where
    right : [¬ (¬ (¬ p))] `⊢` (¬ (¬ (¬ p)))
    right = Start
      ~~(Assume (¬(¬(¬ p))))

    left : [¬ (¬ p)] `⊢` (¬ (¬ p))
    left = Start
      ~~(Assume (¬(¬ p)))


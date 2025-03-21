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

∨ : Formula -> Formula -> Formula
∨ x y = Or x y

⊥ : Formula
⊥ = Bot

shiftN : Nat -> (l : List a) -> {auto prf : NonEmpty l} -> List a
shiftN _ [] impossible
shiftN 0 b@(x :: xs) = b
shiftN (S n) b@(x :: []) = [x]
shiftN (S n) b@(x :: (y::ys)) = y :: (shiftN n (x::ys))

simpleShiftN : shiftN 3 [0, 1, 2, 3] = [1, 2, 3, 0]
simpleShiftN = Refl

headNth : Nat -> (l : List a) -> List a
headNth = (uncurry headNthHelp) . dup
  where
    headNthHelp : Nat -> Nat -> (l : List a) -> List a
    headNthHelp k 0 l = l
    headNthHelp k (S j) [] = []
    headNthHelp k (S j) (x :: xs) = headNthHelp k j (shiftN k (x::xs))

simpleHeadNth : headNth 3 [0, 1, 2, 3, 4, 5] = [3, 0, 1, 2, 4, 5]
simpleHeadNth = Refl

data Strength = Minimal | Intuitionistic | Classical

Eq Strength where
  (==) Minimal Minimal = True
  (==) Classical Classical = True
  (==) Intuitionistic Intuitionistic = True
  (==) _ _ = False

Ord Strength where
  (<) Minimal Intuitionistic = True
  (<) Minimal Classical = True
  (<) Intuitionistic Classical = True
  (<) _ _ = False

Weakest : Strength
Weakest = Minimal

data Derivation : List Formula -> Strength -> Formula -> Type where
  Empty : Derivation [] Weakest Top

  HeadAsmp : (n : Nat) -> Derivation as s f -> Derivation (headNth n as) s f

  NegI : Derivation (f::as) s Bot -> Derivation as s (Not f)
  NegE : Derivation as s f -> Derivation bs s (Not f) -> Derivation (as ++ bs) s Bot

  AndEL : Derivation as s (And f g) -> Derivation as s f
  AndER : Derivation as s (And f g) -> Derivation as s g
  AndI  : Derivation as s f -> Derivation bs s g -> Derivation (as ++ bs) s (And f g)

  OrE  : Derivation (f::bs) s h -> Derivation (g::cs) t h -> Derivation as u (Or f g) -> Derivation (bs ++ cs ++ as) (max (max s t) u) h
  OrIL : (g : Formula) -> Derivation as s f -> Derivation as s (Or g f)
  OrIR : (g : Formula) -> Derivation as s f -> Derivation as s (Or f g)

  ImpE : Derivation as s f -> Derivation bs s (If f g) -> Derivation (as ++ bs) s g
  ImpI : Derivation (f :: as) s g -> Derivation as s (If f g)

  -- structural rules
  THIN : Derivation as s f -> Derivation bs s g -> Derivation as s f
  Assume : (g : Formula) -> Derivation as s f -> Derivation (g :: as) s g

  -- intuitionistic rules
  EFQ : (f : Formula) -> Derivation as s Bot -> Derivation as (max s Intuitionistic) f

  -- 'classical' rules
  TNDL : (a : Formula) -> Derivation as _ f -> Derivation as Classical (Or a (Not a))
  TNDR : (a : Formula) -> Derivation as _ f -> Derivation as Classical (Or (Not a) a)

  CR  : Derivation ((Not p)::as) _ Bot -> Derivation as Classical p

data Step : List Formula -> Strength -> (f : Formula) -> (g : Formula) -> Type where
  Start     : Step [] Weakest Top Top
  OneRule   : Step xs s a b -> (Derivation xs s b -> Derivation ys t c) -> Step ys (max s t) a c
  TwoRule   : (Step xs s a b, Step ys t a c) -> (Derivation xs s b -> Derivation ys t c -> Derivation zs u d) -> Step zs (max (max s t) u) a d
  ThreeRule : (Step xs s a b, Step ys t a c, Step zs u a d) -> (Derivation xs s b -> Derivation ys t c -> Derivation zs u d -> Derivation us v e) -> Step us (max (max (max s t) u) v) a e

(~~) : Step xs s a b -> (Derivation xs s b -> Derivation ys t c) -> Step ys (max s t) a c
(~~) = OneRule

(~~~) : (Step xs s a b, Step ys t a c) -> (Derivation xs s b -> Derivation ys t c -> Derivation zs u d) -> Step zs (max (max s t) u) a d
(~~~) = TwoRule

(~~~~) : (Step xs s a b, Step ys t a c, Step zs u a d) -> (Derivation xs s b -> Derivation ys t c -> Derivation zs u d -> Derivation us v e) -> Step us (max (max (max s t) u) v) a e
(~~~~) = ThreeRule

infixl 5 ~~
infixl 5 ~~~
infixl 5 ~~~~

infixl 5 |?~
infixl 5 |~
infixl 5 |!~
infixl 5 |.~
infixl 5 ~?

(|?-) : List Formula -> Strength -> Formula -> Type
(|?-) = curry $ (flip . uncurry $ Step) Top

-- minimal derivation
(|~) : List Formula -> Formula -> Type
(|~) = (flip $ (flip Step) Minimal) Top

-- intuitionistic derivation
(|!~) : List Formula -> Formula -> Type
(|!~) = (flip $ (flip Step) Intuitionistic) Top

-- classical derivation
(|.~) : List Formula -> Formula -> Type
(|.~) = (flip $ (flip Step) Classical) Top

∵ : (Derivation [] Weakest Top -> Derivation ys s c) -> Step ys (max Weakest s) Top c
∵ = OneRule Start

ex1 : {p : Formula} -> [p] |~ (¬(¬ p))
ex1 = 
  (left, right)
  ~~~ NegE
  -- [p, ¬ p] `⊢` ⊥
  ~~ (HeadAsmp 1)
  -- [¬ p, p] `⊢` ⊥
  ~~ NegI
  where
    left : [p] |~ p
    left = ∵ (Assume p)

    right : [¬ p] |~ (¬ p)
    right = ∵ (Assume $ ¬ p)

ex2 : {p : Formula} -> [¬ (¬ (¬ p))] |~ (¬ p)
ex2 = 
  (ex1, right)
  ~~~ NegE
  -- [p, ¬ (¬ (¬ p))] `⊢` ⊥
  ~~ NegI
  where
    right : [¬ (¬ (¬ p))] |~ (¬ (¬ (¬ p)))
    right = ∵ (Assume (¬ (¬ (¬ p))))

ex3 : {p, q, r : Formula} -> [r, (r `→` q), p `→` (¬ q)] |~ (¬ p)
ex3 =
  (left, right)
  ~~~ NegE
    -- [r, r `→` q, p, p `→` (¬ q)] `⊢` ⊥
  ~~ (HeadAsmp 2)
    -- [p, r, r `→` q, p `→` (¬ q)] `⊢` ⊥
  ~~ NegI
  where
    left : [r, r `→` q] |~ q
    left = 
      (∵ $ Assume r, ∵ $ Assume (r `→` q)) ~~~ ImpE

    right : [p, p `→` (¬ q)] |~ ¬ q
    right =
      (∵ $ Assume p, ∵ $ Assume (p `→` (¬ q))) ~~~ ImpE

ex4 : {p, q : Formula} -> [¬ p] |!~ (p `→` q)
ex4 =
  (∵ $ Assume p, ∵ $ Assume (¬ p))
  ~~~ NegE
  -- [p, ¬ p] `⊢` ⊥
  ~~ (EFQ q)
  -- [p, ¬ p] `⊢` q
  ~~ ImpI

ex5 : {p, q : Formula} -> [] |.~ ((p `→` q) `∨` (q `→` p))
ex5 =
  (left, middle, right)
  ~~~~ OrE
  where
    left : [¬ p] |!~ ((p `→` q) `∨` (q `→` p))
    left =
      (∵ $ Assume p, ∵ $ Assume (¬ p))
      ~~~ (NegE)
      -- [p, ¬ p] `⊢` ⊥
      ~~ (EFQ q)
      -- [p, ¬ p] `⊢` q
      ~~ (ImpI)
      -- [¬ p] `⊢` (p `→` q)
      ~~ OrIR(q `→` p)

    middle : [p] |~ ((p `→` q) `∨` (q `→` p))
    middle =
      ∵ (Assume q)
      -- [q] `⊢` q
      ~~(Assume p)
      -- [p, q] `⊢` p
      ~~(HeadAsmp 1)
      -- [q, p] `⊢` p
      ~~(ImpI)
      -- [p] `⊢` (q `→` p)
      ~~OrIL(p `→` q)

    right : [] |.~ ((¬ p) `∨` p)
    right = Start ~~ (TNDR p)

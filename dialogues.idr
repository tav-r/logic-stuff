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

Atomic : Formula -> Type
Atomic (Atom x) = ()
Atomic _ = Void

pAssertable : List Formula -> Formula -> Type
pAssertable fs f = Either (Not $ Atomic f) (Contains fs f)

data Attack = ConjL Formula | ConjR Formula | Disj Formula | Imp Formula | Neg Formula

mutual
  data PTurn : (passertions, oassertions : List Formula) -> (pattacks, oattacks : List Attack) -> Type where
    -- defenses
    PClaim : (f : Formula) -> PTurn [f] [] [] []

    PConjLD : OTurn pc oc pa ((ConjL (a && b))::oa) -> {auto _ : pAssertable oc a} -> PTurn (a::pc) oc pa oa
    PConjRD : OTurn pc oc pa ((ConjL (a && b))::oa) -> {auto _ : pAssertable oc b} -> PTurn (b::pc) oc pa oa

    PDisjDL : OTurn pc oc pa ((Disj (a || b))::oa) -> {auto _ : pAssertable oc a} -> PTurn (a::pc) oc pa oa
    PDisjDR : OTurn pc oc pa ((Disj (a || b))::oa) -> {auto _ : pAssertable oc b} -> PTurn (b::pc) oc pa oa

    PImpD : OTurn pc oc pa ((Imp (a =.> b))::oa) -> {auto _ : pAssertable oc b} -> PTurn (b::pc) oc pa oa

    -- attacks
    PConjLA : PTurn pc oc pa oa -> {auto prf : Contains oc (And a b)} -> PTurn (discharge oc (And a b) prf) oc pa ((ConjL (a && b))::oa)
    PConjRA : PTurn pc oc pa oa -> {auto prf : Contains oc (And a b)} -> PTurn (discharge oc (And a b) prf) oc pa ((ConjR (a && b))::oa)

    PDisjA : PTurn pc oc pa oa -> {auto prf : Contains oc (Or a b)} -> PTurn (discharge oc (Or a b) prf) oc pa ((Disj (a || b))::oa)

    PImpA : PTurn pc oc pa oa -> {auto prf : Contains oc (a =.> b)} -> PTurn (discharge oc (a =.> b) prf) (a::oc) pa ((Imp (a =.> b))::oa)

    PNegA : PTurn pc oc pa oa -> {auto prf : Contains oc (¬ a)} -> PTurn (discharge oc (¬ a) prf) (a::oc) pa ((Neg (¬ a))::oa)

  data OTurn : (passertions, oassertions : List Formula) -> (pattacks, oattacks : List Attack) -> Type where
    -- defenses
    OConjLD : PTurn pc oc pa ((ConjL (a && b))::oa) -> OTurn (a::pc) oc pa oa
    OConjRD : PTurn pc oc pa ((ConjL (a && b))::oa) -> OTurn (b::pc) oc pa oa

    ODisjDL : PTurn pc oc pa ((Disj (a || b))::oa) -> OTurn (a::pc) oc pa oa
    ODisjDR : PTurn pc oc pa ((Disj (a || b))::oa) -> OTurn (b::pc) oc pa oa

    OImpD : OTurn pc oc pa ((Imp (a =.> b))::oa) -> OTurn (b::pc) oc pa oa

    -- attacks
    OConjLA : PTurn ((And a b)::pc) oc pa oa -> OTurn pc oc pa ((ConjL (a && b))::oa)
    OConjRA : PTurn ((And a b)::pc) oc pa oa -> OTurn pc oc pa ((ConjR (a && b))::oa)

    ODisjA : PTurn ((Or a b)::pc) oc pa oa -> OTurn pc oc pa ((Disj (a || b))::oa)

    OImpA : PTurn ((a =.> b)::pc) oc pa oa -> OTurn pc (a::oc) pa ((Imp (a =.> b))::oa)

    ONegA : PTurn ((¬ a)::pc) oc pa oa -> OTurn pc (a::oc) pa ((Neg (¬ a))::oa)

phi : {p : Type} -> Formula
phi = Atom p

psi : {q : Type} -> Formula
psi = Atom q

-- This code implements the fragment described in "Rethinking scope islands"
-- See github.com/cb125/scope-islands
-- load into ghci, then type "main"

import Prelude hiding ((<>))
import Data.List
import Text.PrettyPrint
import Debug.Trace

abstractionBudget = 1

-- Data structures: Formulas, semantic Terms, syntactic Structures, Proofs:
data For = DP | S | N | T | F
              | FS Int For For | BS Int For For deriving (Eq, Show)
data Ter = Op String | Var Int | Lam Int Ter | App Ter Ter deriving (Eq, Show)
data Str = Leaf Ter For | Node Int Str Str | I | B | C deriving (Eq, Show)
data Proof = Proof String Str For [Proof] Ter deriving Show
instance Eq Proof where (Proof _ b c _ e) == (Proof _ w x _ z)
                          = (b == w) && (c == x) && e == z

focus :: Str -> [Str]
focus s = case s of 
  Node i l r ->    [Node 0 s I]
                ++ [Node j f (Node i c (Node 0 r B)) | Node j f c <- focus l]
                ++ [Node j f (Node i l (Node 0 c C)) | Node j f c <- focus r]
  _ -> [Node 0 s I]

plug :: Str -> Str
plug s = case s of
  Node _ f I -> f
  Node m f (Node n c (Node _ r B)) -> Node n (plug (Node m f c)) r
  Node m f (Node n l (Node _ c C)) -> Node n l (plug (Node m f c))
  _ -> s

reducible :: Str -> Bool -- tests for scope island violation
reducible s = case s of
  Node _ _ I -> True
  Node m f (Node n c (Node _ _ B)) -> (m >= n) && reducible (Node m f c)
  Node m f (Node n _ (Node _ c C)) -> (m >= n) && reducible (Node m f c)
  _ -> True

isContext :: Str -> Bool
isContext (Node _ _ (Node _ _ s)) = s == B || s == C
isContext s = s == I

term (Proof s l r ps t) = t

-- n is the number of nested abstractions, i is the next unused variable index
prove :: Str -> For -> Int -> Int -> [Proof]
prove l r n i = let agenda = focus l in

--  trace (show ((prettySeq l r), n)) [] ++
--  trace (show (l, r, n)) [] ++

  nub (concat [
    [Proof "Ax" l r [] t | Leaf t r' <- [l], r' == r],

    [Proof "Red" l r [x] (term x)
      | Node m p c <- [l]
      , m > 0
      , isContext c
      , reducible l
      , x <- prove (plug l) r (n-1) i],

    [Proof "EXP" l r [x] (term x)
      | n < abstractionBudget
      , Node _ f c <- agenda
      , c /= I, f /= I
      , x <- prove (Node 0 f c) r (n+1) i],

    [Proof "/R" l r [x] (Lam i (term x))
      | FS m c b <- [r]
      , x <- prove (Node m l (Leaf (Var i) b)) c n (i+1)],

    [Proof "\\R" l r [x] (Lam i (term x)) 
      | BS m a c <- [r]
      , x <- prove (Node m (Leaf (Var i) a) l) c n (i+1)],

    [Proof "/L" l r [x, y] (term y) 
      | Node _ (Node m (Leaf tl (FS m' b a)) gam)  c <- agenda
      , m == 0 || m >= m'
      , x <- prove gam a n i
      , y <- prove (plug (Node m (Leaf (App tl (term x)) b) c)) r n i],

    [Proof "\\L" l r [x, y] (term y) 
      | Node _ (Node m gam (Leaf tl (BS m' a b))) c <- agenda
      , m == 0 || m >= m'
      , x <- prove gam a n i
      , y <- prove (plug (Node m (Leaf (App tl (term x)) b) c)) r n i]
    ])

try :: (Str, For) -> [Doc]
try (s, f) = map (\p -> (text "\n") <> -- prettyTerm (term p) $+$
                                         prettyTerm (etaReduce (term p)) $+$
--                        prettyProof p $+$  -- uncomment to see derivation
                           (text "\n"))
                 (prove s f 0 0)

etaReduce :: Ter -> Ter
etaReduce (Lam i (App t (Var i'))) =
  if (i == i') then etaReduce t else (Lam i (App (etaReduce t) (Var i')))
etaReduce (App t1 t2) = App (etaReduce t1) (etaReduce t2)
etaReduce t = t

-- =============================================================================

ann = Leaf (Op "ann") DP
bill = Leaf (Op "bill") DP
dog = Leaf (Op "dog") N
left = Leaf (Op "left") (BS 0 DP S)
the = Leaf (Op "the") (FS 0 DP N)
saw = Leaf (Op "saw") (FS 0 (BS 0 DP S) DP)
noone = Leaf (Op "no one") (FS 0 S (BS 0 DP S))
everyone = Leaf (Op "everyone") (FS 0 S (BS 1 DP S))
anyone = Leaf (Op "anyone") (FS 0 S (BS 2 DP S))
someone = Leaf (Op "someone") (FS 0 S (BS 3 DP S))
ensured = Leaf (Op "ensured") (FS 1 (BS 0 DP S) S)
thought = Leaf (Op "thought") (FS 2 (BS 0 DP S) S)
doubts = Leaf (Op "doubts") (FS 3 (BS 0 DP S) S)
only = Leaf (Op "only") (FS 4 (BS 0 DP S) F)
foc = Leaf (Op "foc") (FS 0 (FS 0 F (BS 4 DP (BS 0 DP S))) DP)
damn = Leaf (Op "damn") (FS 0 T (BS 4 (FS 0 N N) S))

p1 = (Node 0 ann left, S)
p2 = (Node 0 everyone left, S)
p3 = (Node 0 ann (Node 0 saw everyone), S)

ex81 = (Node 0 someone (Node 1 ensured (Node 0 noone left)), S)
ex82 = (Node 0 someone (Node 1 ensured (Node 0 everyone left)), S)

ex83 = (Node 0 ann (Node 2 thought (Node 0 everyone left)), S)
ex84 = (Node 0 ann (Node 2 thought (Node 0 someone left)), S)

ex85 = (Node 0 ann (Node 3 doubts (Node 0 anyone left)), S)
ex86 = (Node 0 ann (Node 3 doubts (Node 0 someone left)), S)

ex87 = (Node 0 ann
          (Node 4 only
             (Node 2 thought 
                (Node 0 someone (Node 0 saw (Node 0 foc bill))))), S)

ex88 = (Node 0 ann
          (Node 4 only
             (Node 2 thought 
                (Node 0 (Node 0 the (Node 0 damn dog))
                   (Node 0 saw (Node 0 foc bill))))), T)

-- =============================================================================

prettyProof :: Proof -> Doc
prettyProof (Proof "Ax" l r ps _) = text "  " <> prettySeq l r
prettyProof (Proof rule l r [x] _) =
  text "  " <> (prettyProof x $+$ prettySeq l r <> text (" _" ++ rule))
prettyProof (Proof rule l r [x,y] _) =
  text "  " <> (prettyProof x $+$ prettyProof y $+$ prettySeq l r
            <> text (" _" ++ rule))

prettySeq :: Str -> For -> Doc
prettySeq s f = prettyStr s <+> text "|-" <+> prettyFor f

vars = "xyz"++['a'..'w']

prettyStr :: Str -> Doc
prettyStr (Leaf (Var i) S) = char (vars!!i)
prettyStr (Leaf t@(Op word) _) = prettyTerm t
prettyStr (Leaf t f) = prettyFor f
prettyStr s@(Node m l r) = prettyNode 0 s
prettyStr s = text (show s)

prettyNode, prettyNode' :: Int -> Str -> Doc
prettyNode v s@(Node m l r) = if isContext s
  then text "\\" <> (char (vars!!v))
                 <> prettyNode' (v+1) (plug (Node m (Leaf (Var v) S) s))
  else prettyNode' v l
          <+> text (show m)
          <+> prettyNode' v r
prettyNode' v s@(Node _ _ _) = parens (prettyNode v s)
prettyNode' v s = prettyStr s

prettyFor, prettyFor' :: For -> Doc
prettyFor (BS m l r) =
  prettyFor' l <> text "\\" <> text (show m) <> prettyFor' r
prettyFor (FS m l r) = prettyFor' l <> text "/" <> text (show m) <> prettyFor' r
prettyFor  a          = text (show a)
prettyFor' a@(FS _ _ _) = parens (prettyFor a)
prettyFor' a@(BS _ _ _) = parens (prettyFor a)
prettyFor' a          =         prettyFor a

prettyTerm :: Ter -> Doc
prettyTerm (Op s) = text s
prettyTerm (Var i) = char (vars!!i)
prettyTerm (Lam i t) = parens (char '\\' <> char (vars!!i) <+> prettyTerm t)
prettyTerm (App t1 t2) = parens ((prettyTerm t1) <+> (prettyTerm t2))

main = print $ map try [ex81, ex82, ex83, ex84, ex85, ex86, ex87, ex88]

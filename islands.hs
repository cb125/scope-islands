import Data.List
import Text.PrettyPrint
import Debug.Trace

abstractionBudget = 1
inf = 9

-- Data structures: Formulas, semantic Terms, syntactic Structures, Proofs:
data For = DP | S | N | T | F
              | FS Int For For | BS Int For For deriving (Eq, Show)
data Ter = Op String | Var Int | Lam Int Ter | App Ter Ter deriving (Eq, Show)
data Str = Leaf Ter For | Node Int Str Str | I | B | C deriving (Eq, Show)
data Proof = Proof String Str For [Proof] Ter deriving Show
instance Eq Proof where (Proof _ b c _ e) == (Proof _ w x _ z)
                          = (b == w) && (c == x) && e == z

focus :: Str -> [(Str, Str)]
focus s = case s of 
  Node m l r ->    [(s,I)]
                ++ [(f, Node m c (Node m r B)) | (f, c) <- focus l]
                ++ [(f, Node m l (Node m c C)) | (f, c) <- focus r]
  _ -> [(s,I)]

plug :: Str -> Str
plug s = case s of
  Node _ f I -> f
  Node m f (Node m' c (Node m'' r B)) -> Node (min m m') (plug (Node m f c)) r
  Node m f (Node m' l (Node m'' c C)) -> Node (min m m') l (plug (Node m f c))
  _ -> s

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
      , x <- prove (plug l) r (n-1) i],

    [Proof "EXP" l r [x] (term x)
      | n < abstractionBudget
      , (f, c) <- agenda
      , c /= I, f /= I
      , x <- prove (Node 0 f c) r (n+1) i],

    [Proof "/R" l r [x] (Lam i (term x))
      | FS m c b <- [r]
      , x <- prove (Node m l (Leaf (Var i) b)) c n (i+1)],

    [Proof "\\R" l r [x] (Lam i (term x)) 
      | BS m a c <- [r]
      , x <- prove (Node m (Leaf (Var i) a) l) c n (i+1)],

    [Proof "/L" l r [x, y] (term y) 
      | (Node m (Leaf tl (FS m' b a)) gam, c) <- agenda
      , m == 0 || m >= m'
      , x <- prove gam a n i
      , y <- prove (plug (Node m (Leaf (App tl (term x)) b) c)) r n i],

    [Proof "\\L" l r [x, y] (term y) 
      | (Node m gam (Leaf tl (BS m' a b)), c) <- agenda
      , m == 0 || m >= m'
      , x <- prove gam a n i
      , y <- prove (plug (Node m (Leaf (App tl (term x)) b) c)) r n i]
    ])

try :: (Str, For) -> [Doc]
try (s, f) = map (\p -> (text "\n\n") <> -- prettyTerm (term p) $+$
                                         prettyTerm (etaReduce (term p)) $+$
--                        prettyProof p
--                         $+$ text (show (s,f)) <>
                           (text "\n\n"))
                 (prove s f 0 0)

etaReduce :: Ter -> Ter
etaReduce (Lam i (App t (Var i'))) =
  if (i == i') then etaReduce t else (Lam i (App (etaReduce t) (Var i')))
-- etaReduce (Pair t1 t2) = Pair (etaReduce t1) (etaReduce t2)
etaReduce (App t1 t2) = App (etaReduce t1) (etaReduce t2)
etaReduce t = t

-- =============================================================================

ann = Leaf (Op "ann") DP
bill = Leaf (Op "bill") DP
carl = Leaf (Op "carl") DP
left = Leaf (Op "left") (BS 1 DP S)
saw = Leaf (Op "saw") (FS 1 (BS 1 DP S) DP)
the = Leaf (Op "the") (FS 1 DP N)
same = Leaf (Op "same") (FS 1 (BS 1 DP S) (BS 1 (FS 1 N N) (BS 1 DP S)))
book = Leaf (Op "book") N
tsb = Leaf (Op "tsb") (FS 1 (BS 1 DP S) (BS 1 DP (BS 1 DP S)))
today = Leaf (Op "today") (BS 1 (BS 1 DP S) (BS 1 DP S))
thought = Leaf (Op "thought") (FS 2 (BS 1 DP S) S)
xif = Leaf (Op "if") (FS 4 (FS 1 S S) S)
someone = Leaf (Op "someone") (FS 1 S (BS 5 DP S))
anyone = Leaf (Op "anyone") (FS 1 S (BS 3 DP S))
everyone = Leaf (Op "everyone") (FS 1 S (BS 1 DP S))
a = Leaf (Op "a") (FS 1 (FS 1 S (BS 1 DP S)) N)
bee = Leaf (Op "bee") N
dog = Leaf (Op "dog") N
man = Leaf (Op "man") N
woman = Leaf (Op "woman") N
people = Leaf (Op "people") N
red = Leaf (Op "red") (FS 1 N N)
damn = Leaf (Op "damn") (FS 1 T (BS 8 (FS 1 N N) S))
only = Leaf (Op "only") (FS 7 (BS 1 DP S) F)
foc = Leaf (Op "foc") (FS 1 (FS 6 F (BS 6 DP (BS 6 DP S))) DP)

p1 = (Node inf ann (Node inf thought (Node inf everyone left)), S)
p2 = (Node inf ann (Node inf thought (Node inf someone left)), S)
p3 = (Node inf ann (Node inf only (Node inf thought (Node inf someone
       (Node inf saw (Node inf foc bill))))), S)
p4 = (Node inf ann (Node inf only (Node inf thought (Node inf
       (Node inf the (Node inf damn dog)) (Node inf saw (Node inf foc
       bill))))), T)

regression = map try [p1, p2, p3, p4] 

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
          <+> text (if m == inf then "." else (show m))
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

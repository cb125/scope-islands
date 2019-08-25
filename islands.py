import functools

class For: # formula
    def __init__(self, left, connector = None, right = None, level = 0):
        self.l = left
        self.c = connector
        self.r = right
        self.level = level
        if self.c == None: self.count = 0
        else: self.count = 1 + self.l.count + self.r.count
        if self.c == None: self.string = self.l
        else:
          if self.level == 0:
            self.string = "(" + self.l.string + self.c + self.r.string + ")"
          else:
            self.string = "(" + self.l.string + str(self.level) + self.c + self.r.string + ")"

class Struc: # branching structure
    def __init__(self, left, connector, right):
        self.l = left
        self.c = connector
        self.r = right
        self.isLeaf = False
        self.isStruc = True
        self.count = self.l.count + self.r.count
        self.isContext = self.r.isStruc and (self.r.r == b or self.r.r == c)
        if self.c == 0: 
            self.string = "[" + self.l.string + " " + "*" + " " + self.r.string + "]"
        else:
            self.string = "[" + self.l.string + " " + str(self.c) + " " + self.r.string + "]"

class Leaf: # non-branching structure
    def __init__(self, formula, term):
        self.form = formula
        self.isLeaf = True
        self.isStruc = False
        self.isContext = False
        self.count = self.form.count
        self.term = term
        self.string = self.form.string

class Combinator: # structural punctuation mark, either I, B, or C
    def __init__(self, string, isContext = False):
        self.isLeaf = False
        self.isStruc = False
        self.isContext = isContext
        self.string = string
        self.count = 0

class Proof:
    def __init__(self, ruleName, lhs, rhs, i, proof1 = None, proof2 = None):
        self.ruleName = ruleName
        self.lhs = lhs
        self.goal = rhs
        self.premise1 = proof1
        self.premise2 = proof2
        if self.ruleName == "Axiom":
            self.term = self.lhs.term
        elif self.ruleName == "\\R" or self.ruleName == "/R" or self.ruleName == "TRACE":
            self.term = ("(\\" + str(i) + " " + self.premise1.term + ")")
        elif self.ruleName == "\\L" or self.ruleName == "/L":
            self.term = self.premise2.term
        elif self.ruleName == "RED" or self.ruleName == "EXP":
            self.term = self.premise1.term
        self.string = self.lhs.string + " |- " + self.goal.string
    def __eq__(self, other):
        return(other != None and self.string == other.string and self.term == other.term)
    def __hash__(self):
        return(hash(self.term))
    def proofString(self, indent = "  "):
        prems = ""
        if self.premise1 != None:
            prems += self.premise1.proofString(indent + "  ")
        if self.premise2 != None:
            prems += self.premise2.proofString(indent + "  ")
        return(prems + indent + self.string + "  " + self.ruleName + "\n")

i = Combinator("I", True)
b = Combinator("B")
c = Combinator("C")
unit = Combinator("1")

@functools.lru_cache(maxsize=None)
def foci(s):
    if s.isLeaf: return([(s, i)])
    elif not s.isStruc: return([])
    else:
        pairs = []
        if s.r != b and s.r != c: pairs = [(s,i)]
        return(pairs
               + [(foc, Struc(con, s.c, Struc(s.r, 0, b)))
                 for foc, con in foci(s.l)]
               + [(foc, Struc(s.l, s.c, Struc(con, 0, c)))
                 for foc, con in foci(s.r)])

@functools.lru_cache(maxsize=None)
def plug(foc, con, level = 0, reduction = False):
    if not con.isContext: raise(Exception)
    if con == i: return(foc)
    elif con.r.r == b:
        if reduction and level <= con.c: pass
        else: return(Struc(plug(foc, con.l, level, reduction), con.c, con.r.l))
    elif con.r.r == c:
        if reduction and level <= con.c: pass
        else: return(Struc(con.l, con.c, plug(foc, con.r.l, level, reduction)))

@functools.lru_cache(maxsize=None)
def prove(l,r,b,i): #Struc, For, expansion budget, least unused variable index

#    print(l.string, "|-", r.string, b, i)

    b = min(b, int((l.count + r.count)/2))

    if l.isLeaf and l.form.string == r.string: return([Proof("Axiom", l, r, i)])

    proofs = []

    if r.c == "\\":
        proofs += [Proof("\\R", l, r, str(i), x) for x in
                   prove(Struc(Leaf(r.l, str(i)), r.level, l), r.r, b, i+1)]

    if r.c == "/":
        proofs += [Proof("/R", l, r, str(i), x) for x in
                   prove(Struc(l, r.level, Leaf(r.r, str(i))), r.l, b, i+1)]

    for (foc, con) in foci(l):

        if (foc.isStruc and foc.r.isLeaf and foc.r.form.c == '\\'):
           proofs += [Proof("\\L", l, r, i, x, y) 
                        for x in prove(foc.l, foc.r.form.l, b, i)
                        for y in prove(plug(Leaf(foc.r.form.r,
                                                 ("(" + foc.r.term + " "
                                                  + x.term + ")")),
                                            con), r, b, i)]

        if (foc.isStruc and foc.l.isLeaf and foc.l.form.c == "/"):
           proofs += [Proof("/L", l, r, i, x, y)
                        for x in prove(foc.r, foc.l.form.r, b, i)
                        for y in prove(plug(Leaf(foc.l.form.l,
                                                 ("(" + foc.l.term + " "
                                                  + x.term + ")")),
                                            con), r, b, i)]

        if foc.isStruc and foc.r.isContext:

           try:
                proofs += [Proof("RED", l, r, i, x)
                          for x in prove(plug(plug(foc.l, foc.r, foc.c, True), con),
                                         r, b, i)]
           except:
               pass

        for (foc2, con2) in foci(foc):
           if foc2.isLeaf and b > 0:
             proofs += [Proof("EXP", l, r, i, x)
                        for x in prove(plug(Struc(foc2, 0, con2), con),
                                       r, b-1, i)]

    return(set(proofs)) # delete "set" to get all proof variants

dp = For("DP")
s = For("S")
q = For("Q")
nom = For("N")
f = For("F")
top = For("T")

def build(s):
    if isinstance(s, Leaf): return(s)
    elif len(s) == 2: return(Struc(build(s[0]), 0, build(s[1])))
    elif len(s) == 3: return(Struc(build(s[0]), s[1], build(s[2])))

def sentenceToString(s):
    if isinstance(s, Leaf): return(s.term)
    elif len(s) == 2: return(sentenceToString(s[0]) + " " + sentenceToString(s[1]))
    elif len(s) == 3: return(sentenceToString(s[0]) + " " + sentenceToString(s[2]))

def do (sentence, goal=s, budget = 1):
   sen = build(sentence)
   print(sentenceToString(sentence))
   list(map(lambda x: print(x.term, ":\n", x.proofString()),
            prove(sen, goal, budget, 0)))

ann = Leaf(dp, "ann")
bill = Leaf(dp, "bill")
carl = Leaf(dp, "carl")
left = Leaf(For(dp, "\\", s), "left")
saw = Leaf(For(For(dp, "\\", s), "/", dp), "saw")
gave = Leaf(For(For(For(dp, "\\", s), "/", dp), "/", dp), "gave")
thought = Leaf(For(For(dp, "\\", s), "/", s, 2), "thought")
xif = Leaf(For(For(s, "/", s), "/", s, 3), "if")
everyone = Leaf(For(s, "/", For(dp, "\\", s)), "everyone")
someone = Leaf(For(s, "/", For(dp, "\\", s, 4)), "someone")
anyone = Leaf(For(s, "/", For(dp, "\\", s, 3)), "anyone")
a = Leaf(For(For(s, "/", For(dp, "\\", s)), "/", nom), "a")
the = Leaf(For(dp, "/", nom), "the")
bee = Leaf(nom, "bee")
dog = Leaf(nom, "dog")
man = Leaf(nom, "man")
woman = Leaf(nom, "woman")
people = Leaf(nom, "people")
red = Leaf(For(nom, "/", nom), "red")
damn = Leaf(For(top, "/", For(For(nom, "/", nom), "\\", s, 6)), "damn")
tdd = Leaf(For(top, "/", For(dp, "\\", s, 6)), "the-damn-dog")
someof = Leaf(For(dp, "/", dp), "part")
same = Leaf(For(For(dp, "\\", s), "/",
                For(For(nom, "/", nom), "\\", For(dp, "\\", s))), "same")
mssame = Leaf(For(For(For(dp, "\\", s), "/", For(dp, "\\", For(dp, "\\", s))),
                     "/", For(For(nom, "/", nom), "\\", dp)), "mssame")
who1 = Leaf(For(q, "/", For(unit, "x", For(dp, "\\", s))), "who1")
who = Leaf(For(q, "/", For(dp, "\\", s)), "who")
bidk = Leaf(For(For(s, "\\", s), "/", q), "bidk")
sg = Leaf(For(For(For(dp, "\\", s), "\\", s), "/", 
              For(For(dp, "\\", s), "\\", For(For(dp, "\\", s), "\\", s))),
          "sg")
foc = Leaf(For(For(f, "/", For(dp, "\\", For(dp, "\\", s, 4), 4)), "/", dp), "foc")
only = Leaf(For(For(dp, "\\", s), "/", f, 4), "only")

#do((ann, left))
#do((everyone, left))
#do((ann, (saw, everyone)))
#do((someone, (saw, everyone)))
#do((ann, (saw, (the, (same, bee)))))
#do(((the, (same, bee)), (saw, ann)))
#do(((the, (same, bee)), (saw, everyone)))

#do((ann, ((gave, (the, (same, man))), (the, (same, bee)))), 2)
#do(((the, (same, man)), ((gave, (a, woman)), (the, (same, bee)))), 3)
#do((who, (ann, saw)))

#do((ann, (saw, (someof, (the, (same, people))))))

#do((who, left))
#do((someone, left))
#do(((ann, left), (bidk, (who, left))))
#do(((someone, left), (bidk, (who, left))))
#do(((someone, left), (bidk, (who, sg))))
#do(((bill, (saw, ann)), (bidk, (who, sg))))
#do(((bill, (saw, someone)), (bidk, (who, sg))), 3)

#do((ann, (only, (saw, (foc, bill)))))

do((ann, (thought, 2, (everyone, left))))
do((ann, (thought, 2, (someone, left))))
#do((ann, (only, 4, (thought, 1, (bill, (saw, (foc, carl)))))))
#do((ann, (only, 4, (thought, 1, (everyone, (saw, (foc, carl)))))))

#do((ann, (only, 4, (thought, 2, (someone, (saw, (foc, carl)))))))
#do(((xif, 3, (someone, left)), (ann, left)))
#do(((xif, 3, (anyone, left)), (ann, left)))
#do(((xif, 3, (everyone, left)), (ann, left)))
#do(((xif, 3, (ann, (thought, 2, (someone, left)))), (bill, left)))
#do(((xif, 3, (ann, (thought, 2, (anyone, left)))), (bill, left)))
#do((ann, (thought, 2, ((the, (damn, dog)), left))), top)
#do(((the, (damn, dog)), (only, 4, (thought, 2, (ann, (saw, (foc, carl)))))), top)
#do(((xif, ((the, (damn, dog)), left)), (ann, left)), top)
#do((ann, (only, 4, (saw, (foc, bill)))))
#do((ann, (only, 4, (thought, 2, (someone, (saw, (foc, carl)))))))
#do((ann, (thought, 2, (someone, (saw, carl)))))
#do((ann, (only, 4, (thought, 2, ((the, (red, dog)), (saw, (foc, carl)))))))
##do((ann, (only, 4, (thought, 2, ((the, (damn, dog)), (saw, (foc, carl)))))), top, 2)
#do((ann, (only, 4, (thought, 2, (tdd, (saw, (foc, carl)))))), top, 2)

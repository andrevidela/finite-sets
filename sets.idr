
module Sets

%default total

data Set : a -> Type where
  Empty : Set a
  Singleton : a -> Set a
  Union : Set a -> Set a -> Set a
  Inter : Set a -> Set a -> Set a

-- \included
data IsSubset : Set a -> Set a -> Type where
  SSEmpty  : (s  : Set a) -> IsSubset Empty s -- Empty set is SS of all sets
  SSEq     : {s1 : Set a} -> {s2 : Set a} -> s1 = s2 -> IsSubset s1 s2 -- if s1 = s2 then s1 is SS of s2
  SSUnionl : (s1 : Set a) -> (s2 : Set a) -> IsSubset s1 (Union s1 s2) -- lhs of union is SS of union
  SSUnionr : (s1 : Set a) -> (s2 : Set a) -> IsSubset s1 (Union s2 s1) -- rhs of union is SS of union
  SSInterl : (s1 : Set a) -> (s2 : Set a) -> IsSubset (Inter s1 s2) s1 -- intersection is SS of its lhs
  SSInterr : (s1 : Set a) -> (s2 : Set a) -> IsSubset (Inter s2 s1) s1 -- intersection is SS of its rhs

-- Axioms
postulate IncludeRefl : s1 `IsSubset` s2 -> s2 `IsSubset` s1 -> s1 = s2

postulate emptyUnionIsEmpty : (s: Set a) -> s = Union Empty s

postulate emptyInterIsEmpty : (s : Set a) -> Empty = Inter Empty s

-- Equality proofs

unionAssoc : (s3 : Set a) -> (Union (Union s1 s2) s3) = (Union s1 (Union s2 s3))
unionAssoc {s1} {s2} s3 = ?unionCommute_rhs

singletonEmptyHelp : Union (Singleton x) Empty = Union Empty (Singleton x)
singletonEmptyHelp {x} = let sing = Singleton x 
                             left = SSUnionl (Singleton x) Empty
                             right = SSUnionr (Singleton x) Empty in
                             ?emptysingleton

postulate interSymetric : {s1 : Set a} -> {s2 : Set a} -> (s1 `Inter` s2) = (s2 `Inter` s1)


unionSymetric : {s1 : Set a} -> {s2 : Set a} -> (s1 `Union` s2) = (s2 `Union` s1)
unionSymetric {s1 = Empty} {s2 = Empty} = Refl
unionSymetric {s1 = Empty} {s2 = (Singleton x)} = sym $ singletonEmptyHelp
unionSymetric {s1 = Empty} {s2 = (Union x y)} = ?lhsunionsym_3
unionSymetric {s1 = Empty} {s2 = (Inter x y)} = ?lhsunionsym_4 
unionSymetric {s1 = (Singleton x)} {s2 = s2} = ?unionSingleleft ?unionSymSingle
unionSymetric {s1 = (Union x y)} {s2 = s2} = ?UnionSymetric_rhs_3
unionSymetric {s1 = (Inter x y)} {s2 = s2} = ?UnionSymetric_rhs_4

-- subset proofs
subsetTransitive : {s1 : Set a} -> {s2 : Set a} -> {s3 : Set a} 
-> s1 `IsSubset` s2 -> s2 `IsSubset` s3 -> s1 `IsSubset` s3
subsetTransitive (SSEmpty s2) y = ?subsetTransitive_rhs_1
subsetTransitive (SSEq Refl) y = y
subsetTransitive (SSUnionl s1 s2) y = ?subsetTransitive_rhs_3
subsetTransitive (SSUnionr s1 s2) y = ?subsetTransitive_rhs_4
subsetTransitive (SSInterl s1 s2) y = ?subsetTransitive_rhs_5
subsetTransitive (SSInterr s2 s1) y = ?subsetTransitive_rhs_6

subsetUnionCongruence : {s1 : Set a} -> {s2 : Set a} -> {s3 : Set a} 
  -> s1 `IsSubset` s2 -> (Union s1 s3) `IsSubset` (Union s2 s3)

-- \in 
data IsIn : a -> Set a -> Type where
  InInSingle : a = a -> IsIn a (Singleton a)
  IsInUnion  : IsIn a l -> IsIn a (Union l s)
  IsInInter  : IsIn a l -> IsIn a r -> IsIn a (Inter l r)

isInUnion : IsIn a (Union l r) = IsIn a (Union r l)
isInUnion {l} {r} = rewrite the (Union l r = Union r l) unionSymetric in 
                            Refl

implementation Uninhabited (IsIn a Empty) where
  uninhabited (InInSingle _) impossible
  uninhabited (IsInUnion _) impossible
  uninhabited (IsInInter _ _) impossible
implementation Uninhabited (Empty = Singleton x) where
  uninhabited Refl impossible

voidSingleton : (e = x -> Void) -> IsIn e (Singleton x) -> Void
voidSingleton f (InInSingle Refl) = f Refl

singletonInjective : (x : a) -> (y : a) -> Singleton x = Singleton y -> x = y
singletonInjective y y Refl = Refl

nonEmptyUnionContra : (Empty = r -> Void) -> (Empty = Union l r -> Void)
nonEmptyUnionContra _ Refl impossible




implementation DecEq a => DecEq (Set a) where
  decEq Empty Empty = Yes Refl
  decEq Empty (Singleton x) = No absurd
  decEq Empty (Union x y) with ((decEq Empty x, decEq Empty y))
    decEq Empty (Union x y) | (Yes p, Yes q) = rewrite sym q in
                                               rewrite sym p in Yes $ emptyUnionIsEmpty Empty
    decEq Empty (Union x y) | (Yes _, No  c) = No $ nonEmptyUnionContra c
    decEq Empty (Union x y) | (No  c, _    ) = rewrite the (Union x y = Union y x) unionSymetric in
                                                       No $ nonEmptyUnionContra c
  decEq Empty (Inter x y) with (decEq Empty x, decEq Empty y)
    decEq Empty (Inter x y) | (Yes p, Yes q) = rewrite sym p in 
                                               rewrite sym q in 
                                                       Yes $ emptyInterIsEmpty Empty
    decEq Empty (Inter x y) | (Yes p, No  c) = No ?decEq_rhs
    decEq Empty (Inter x y) | (No  c, Yes p) = ?decEq_rhs
    decEq Empty (Inter x y) | (No  c, No  d) = ?decEq_rhs
  decEq (Singleton x) Empty = No (\c => absurd $ sym c)
  decEq (Singleton x) (Singleton y) with (decEq x y)
    decEq (Singleton y) (Singleton y) | (Yes Refl) = Yes Refl
    decEq (Singleton x) (Singleton y) | (No contra) = No (contra . singletonInjective x y)
  decEq (Singleton x) (Union y z) = ?decEq_rhs_sing
  decEq (Singleton x) (Inter y z) = ?dec_9
  decEq (Union x y) Empty = ?decEq_rhs_1
  decEq (Union x y) (Singleton z) = ?decEq_rhs_2
  decEq (Union x y) (Union z w) with ((decEq x z, decEq y w))
    decEq (Union x y) (Union z w) | (Yes p, Yes q) = rewrite p in 
                                                     rewrite q in Yes Refl
    decEq (Union x y) (Union z w) | (Yes p, No  c) = rewrite p in ?decEq_rhs
    decEq (Union x y) (Union z w) | (No  c, Yes p) = ?decEq_rhs
    decEq (Union x y) (Union z w) | (No  c, No  d) = No ?decEq_rhs
  decEq (Union x y) (Inter z w) = ?decEq_rhs_4
  decEq (Inter x y) s2 = ?dec_4

isInUnionContra : (IsIn e x -> Void) -> IsIn  e (Union x y) -> Void
isInUnionContra contra (IsInUnion x) = contra x

isInInterContra : (IsIn e l -> Void) -> IsIn e (Inter l r) -> Void
isInInterContra contra (IsInInter x y) = contra x

checkInSet : (DecEq a) => (e : a) -> (s : Set a) -> Dec (e `IsIn` s)
checkInSet e Empty = No absurd
checkInSet e (Singleton x) with (decEq e x)
  checkInSet x (Singleton x) | (Yes Refl) = Yes (InInSingle Refl)
  checkInSet e (Singleton x) | (No contra) = No $ voidSingleton contra
checkInSet e (Union x y) with ((checkInSet e x, checkInSet e y))
  checkInSet e (Union x y) | (Yes p, _    ) = Yes $ IsInUnion p
  checkInSet e (Union x y) | (No  c, Yes p) = rewrite the (Union x y = Union y x) unionSymetric in 
                                                      Yes $ IsInUnion p
  checkInSet e (Union x y) | (No  c, No  _) = No (isInUnionContra c)
checkInSet e (Inter x y) with ((checkInSet e x, checkInSet e y))
  checkInSet e (Inter x y) | (Yes p, Yes q) = Yes $ IsInInter p q
  checkInSet e (Inter x y) | (Yes _, No  c) = No $ rewrite the (Inter x y = Inter y x) interSymetric in
                                                           isInInterContra c
  checkInSet e (Inter x y) | (No  c, _    ) = No $ isInInterContra c

listToSet : List a -> Set a
listToSet Nil = Empty
listToSet (x :: xs) = Singleton x `Union` listToSet xs




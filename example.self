def id (A : Type) (x : A) : A = x

def Unit = (A : Type) -> A -> A
def tt : Unit = id

-- test sigma types
def FoldNatTy (Nat : Type) = (A : Type) (n : Nat) (z : A) (s : A -> A) -> A

def NatS =
  (Nat : Type)
  (Z : Nat)
  (S : Nat -> Nat)
  (foldNat : FoldNatTy Nat)
  ** Unit

def NatS-Nat (m : NatS) : Type = fst m
def NatS-Z (m : NatS) : NatS-Nat m = fst (snd m)
def NatS-S (m : NatS) : NatS-Nat m -> NatS-Nat m = fst (snd (snd m))
def NatS-foldNat (m : NatS) : FoldNatTy (NatS-Nat m) = fst (snd (snd (snd m)))
def addS (m : NatS) (a b : NatS-Nat m) = (NatS-foldNat m) (NatS-Nat m) a b (NatS-S m)

-- church natural numbers
def Nat = (A : Type) -> A -> (A -> A) -> A
def Z : Nat = \A z s => z
def S (n : Nat) : Nat = \A z s => s (n A z s)
def foldNat (A : Type) (n : Nat) (z : A) (s : A -> A) : A = n A z s

def NatM : NatS = (Nat, Z, S, foldNat, tt)

def add : Nat -> Nat -> Nat = addS NatM

def n0 = Z
def n1 = S n0
def n2 = S n1
def n3 = S n2

-- test self types
def BoolS = (Bool : Type) ** Bool ** Bool ** Unit
def BoolM : BoolS = in BoolM =>
  let Bool = fst BoolM;
  let True = fst (snd BoolM);
  let False = fst (snd (snd BoolM));
  (
    self b => (P : Bool -> Type) -> P True -> P False -> P b,
    \P t f => t,
    \P t f => f,
    tt
  )

def Bool = fst BoolM
def True : Bool = fst (snd BoolM)
def False : Bool = fst (snd (snd BoolM))
def elimBool (P : Bool -> Type) (t : P True) (f : P False) (b : Bool) : P b = b P t f
def if (A : Type) (b : Bool) (t f : A) : A = elimBool (\_ => A) t f b

-- main will be normalized and displayed
def main = add n3 n3

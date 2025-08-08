def id (A : Type) (x : A) : A = x

def Nat = (A : Type) -> A -> (A -> A) -> A
def Z : Nat = \A z s => z
def S (n : Nat) : Nat = \A z s => s (n A z s)
def foldNat (A : Type) (n : Nat) (z : A) (s : A -> A) : A = n A z s

def add (a b : Nat) = foldNat Nat a b S

def n0 = Z
def n1 = S n0
def n2 = S n1
def n3 = S n2

def main = add n3 n3

def Bool : Type = self (b : Bool) => (P : Bool -> Type) -> P True -> P False -> P b
def True : Bool = in \P t f => t
def False : Bool = in \P t f => f
def indBool (P : Bool -> Type) (t : P True) (f : P False) (b : Bool) : P b =
  out b P t f

def if {A} (b : Bool) (t f : A) : A = indBool (\_ => A) t f b
def not (b : Bool) : Bool = if b False True

def Nat : Type =
  self (n : Nat) => (P : Nat -> Type) -> P Z -> ((m : Nat) -> P (S m)) -> P n
def Z : Nat = in \P z s => z
def S (n : Nat) : Nat = in \P z s => s n
def indNat (P : Nat -> Type) (z : P Z) (s : (m : Nat) -> P m -> P (S m)) (n : Nat) : P n =
  out n P z (\m => s m (indNat P z s m))
def foldNat {A} (n : Nat) (z : A) (s : A -> A) : A =
  indNat (\_ => A) z (\_ => s) n

def n0 = Z
def n1 = S n0
def n2 = S n1
def n3 = S n2

def Vec (n : Nat) (A : Type) : Type =
  self (v : Vec n A) =>
  (P : (n : Nat) -> Vec n A -> Type) ->
  P Z VNil ->
  ({m : Nat} (hd : A) (tl : Vec m A) -> P (S m) (VCons hd tl)) ->
  P n v
def VNil {A} : Vec Z A = in \P nil cons => nil
def VCons {A m} (hd : A) (tl : Vec m A) : Vec (S m) A =
  in \P nil cons => cons hd tl
def indVec {A} (P : (n : Nat) -> Vec n A -> Type)
  (nil : P Z VNil)
  (cons : {m : Nat} (hd : A) (tl : Vec m A) -> P m tl -> P (S m) (VCons hd tl)) (n : Nat) (v : Vec n A) : P n v =
  out v P nil (\{m} hd tl => cons hd tl (indVec P nil cons m tl))

def Id {A} (x y : A) : Type =
  self (id : Id x y) => (P : (y : A) -> Id x y -> Type) -> P x (Refl x) -> P y id
def Refl {A} (x : A) : Id x x = in \P x => x

def rewrite {A} (x y : A) (P : A -> Type) (p : Id x y) (v : P x) : P y =
  out p (\y _ => P y) v

-- testing
def vec = VCons n0 (VCons n1 (VCons n2 VNil))

-- testing proofs
def notnot (b : Bool) : Id (not (not b)) b =
  indBool (\b => Id (not (not b)) b)
    (Refl True)
    (Refl False)
    b

-- testing normalization
def add (a b : Nat) = foldNat a b S
-- def main = add n3 n3 -- loops! :(

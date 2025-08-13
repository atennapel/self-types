def Bool : Type = self (b : Bool) => (P : Bool -> Type) -> P True -> P False -> P b
def True : Bool = in \P t f => t
def False : Bool = in \P t f => f
def indBool (P : Bool -> Type) (t : P True) (f : P False) (b : Bool) : P b =
  out b P t f

def Nat : Type =
  self (n : Nat) => (P : Nat -> Type) -> P Z -> ((m : Nat) -> P (S m)) -> P n
def Z : Nat = in \P z s => z
def S (n : Nat) : Nat = in \P z s => s n
def indNat (P : Nat -> Type) (z : P Z) (s : (m : Nat) -> P m -> P (S m)) (n : Nat) : P n =
  out n P z (\m => s m (indNat P z s m))

def Vec (n : Nat) (A : Type) : Type =
  self (v : Vec n A) =>
  (P : (n : Nat) -> Vec n A -> Type) ->
  P Z (VNil A) ->
  ((m : Nat) (hd : A) (tl : Vec m A) -> P (S m) (VCons A m hd tl)) ->
  P n v
def VNil (A : Type) : Vec Z A = in \P nil cons => nil
def VCons (A : Type) (m : Nat) (hd : A) (tl : Vec m A) : Vec (S m) A =
  in \P nil cons => cons m hd tl
def indVec (A : Type) (P : (n : Nat) -> Vec n A -> Type)
  (nil : P Z (VNil A))
  (cons : (m : Nat) (hd : A) (tl : Vec m A) -> P m tl -> P (S m) (VCons A m hd tl)) (n : Nat) (v : Vec n A) : P n v =
  out v P nil (\m hd tl => cons m hd tl (indVec A P nil cons m tl))

def add (a b : Nat) : Nat = indNat (\_ => Nat) b (\_ => S) a
def n0 = Z
def n1 = S n0
def n2 = S n1
def n3 = S n2
-- def main = add n3 n3
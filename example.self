opaque def Bool = self b => (P : Bool -> Type) -> (True : P True) -> (False : P False) -> P b
def True = in \P t f => t
def False = in \P t f => f
def indBool (P : Bool -> Type) (t : P True) (f : P False) (b : Bool) : P b =
  out b P t f
def if {A} b t f = indBool (\_ => A) t f b
def cond {A} (t f : A) = \b => if b t f
def not = cond False True

opaque def Nat = self n => (P : Nat -> Type) -> (Z : P Z) -> (S : (m : Nat) -> P (S m)) -> P n
def Z = in \P z s => z
def S n = in \P z s => s n
def indNat (P : Nat -> Type) (z : P Z) (s : (m : Nat) -> P m -> P (S m)) (n : Nat) : P n =
  case n : P
  | Z => z
  | S m => s m (indNat P z s m)
def foldNat {A} n z s = indNat (\_ => A) z (\_ => s) n

def pred (n : Nat) =
  case n
  | Z => Z
  | S n => n

def n0 = Z
def n1 = S n0
def n2 = S n1
def n3 = S n2

opaque def Vec n A : Type =
  self v =>
  (P : {n} -> Vec n A -> Type) ->
  (VNil : P VNil) ->
  (VCons : {m} (hd : A) (tl : Vec m A) -> P (VCons hd tl)) ->
  P {n} v
def VNil {A} : Vec Z A = in \P nil cons => nil
def VCons {A m} (hd : A) (tl : Vec m A) : Vec (S m) A =
  in \P nil cons => cons hd tl
def indVec {A} (P : {n} -> Vec n A -> Type)
  (nil : P VNil)
  (cons : {m} (hd : A) (tl : Vec m A) -> P tl -> P (VCons hd tl)) {n} (v : Vec n A) : P v =
  out v P nil (\hd tl => cons hd tl (indVec P nil cons tl))

opaque def Id {A} (x y : A) : Type = self id => (P : {y} -> Id x y -> Type) -> (Refl : P Refl) -> P {y} id
def Refl {A} {x : A} : Id x x = in \P x => x
def rewrite {A} {x y : A} (P : A -> Type) (p : Id x y) (v : P x) : P y =
  out p (\{y} _ => P y) v

opaque def Unit = self u => (P : Unit -> Type) -> P Tt -> P u
def Tt = in \P x => x

def Void = (A : Type) -> A
def absurd {A} (v : Void) : A = v A

def NotId {A} (x y : A) : Type = Id x y -> Void

def notnot (b : Bool) : Id (not (not b)) b =
  indBool (\b => Id (not (not b)) b) Refl Refl b

def true_neq_false : NotId True False =
  \p => rewrite (cond Unit Void) p Tt

def z_neq_s {n} : NotId Z (S n) =
  \p => rewrite {Nat} (case | Z => Unit | S _ => Void) p Tt

def vecHead {n A} (v : Vec (S n) A) : A =
  case v : \{m} v => Id m (S n) -> A with Refl
  | VCons hd _ => \_ => hd
  | VNil => \p => absurd (z_neq_s p)

def vecTail {n A} (v : Vec (S n) A) : Vec n A =
  case v : \{m} v => Id m (S n) -> Vec (pred m) A with Refl
  | VCons _ tl => \_ => tl
  | VNil => \p => absurd (z_neq_s p)

-- testing
def vec = VCons n0 (VCons n1 (VCons n2 VNil))

-- testing normalization
def add (a b : Nat) = foldNat a b S
-- def main = add n3 n3 -- loops! :(

import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.PolynomialUp
import BEDC.Derived.PolynomialUp.Calculus

namespace BEDC.Derived.ResultantUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq
abbrev Poly : Type := BEDC.Derived.PolynomialUp.Poly
abbrev Matrix : Type := List (List Z)

def integerRing : RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev zZero : Z := integerRing.zero
abbrev zOne : Z := integerRing.one
abbrev zAdd : Z -> Z -> Z := integerRing.add
abbrev zMul : Z -> Z -> Z := integerRing.mul
abbrev zNeg : Z -> Z := integerRing.neg
abbrev zSub : Z -> Z -> Z := integerRing.sub

def zTwo : Z :=
  zAdd zOne zOne

def zFour : Z :=
  zMul zTwo zTwo

def zSquare (x : Z) : Z :=
  zMul x x

def coeffAt (p : Poly) (degree : Nat) : Z :=
  BEDC.Derived.PolynomialUp.polyCoeff p degree

def shiftedEntry (p : Poly) (shift column : Nat) : Z :=
  if shift <= column then coeffAt p (column - shift) else zZero

def shiftedRowFrom (p : Poly) (shift column : Nat) : Nat -> List Z
  | 0 => []
  | Nat.succ fuel => shiftedEntry p shift column ::
      shiftedRowFrom p shift (Nat.succ column) fuel

def shiftedRow (p : Poly) (shift width : Nat) : List Z :=
  shiftedRowFrom p shift 0 width

def shiftedRowsFrom (p : Poly) (width shift : Nat) : Nat -> Matrix
  | 0 => []
  | Nat.succ fuel => shiftedRow p shift width ::
      shiftedRowsFrom p width (Nat.succ shift) fuel

def sylvesterMatrix (degreeF degreeG : Nat) (f g : Poly) : Matrix :=
  shiftedRowsFrom f (degreeF + degreeG) 0 degreeG ++
    shiftedRowsFrom g (degreeF + degreeG) 0 degreeF

def rowEraseAt : Nat -> List Z -> List Z
  | _, [] => []
  | 0, _x :: xs => xs
  | Nat.succ column, x :: xs => x :: rowEraseAt column xs

def eraseColumn (column : Nat) (rows : Matrix) : Matrix :=
  rows.map (rowEraseAt column)

def alternatingTerm : Nat -> Z -> Z
  | 0, value => value
  | Nat.succ 0, value => zNeg value
  | Nat.succ (Nat.succ column), value => alternatingTerm column value

def determinantEntries (minorDet : Nat -> Z) : Nat -> Nat -> List Z -> Z
  | 0, _column, _entries => zZero
  | Nat.succ _fuel, _column, [] => zZero
  | Nat.succ fuel, column, entry :: tail =>
      zAdd
        (alternatingTerm column (zMul entry (minorDet column)))
        (determinantEntries minorDet fuel (Nat.succ column) tail)

def determinant : Nat -> Matrix -> Z
  | 0, _rows => zOne
  | Nat.succ _size, [] => zZero
  | Nat.succ size, row :: rows =>
      determinantEntries
        (fun column => determinant size (eraseColumn column rows))
        (Nat.succ size) 0 row

def resultant (degreeF degreeG : Nat) (f g : Poly) : Z :=
  determinant (degreeF + degreeG) (sylvesterMatrix degreeF degreeG f g)

def zPow (x : Z) : Nat -> Z
  | 0 => zOne
  | Nat.succ n => zMul (zPow x n) x

def rootProductValue (leading : Z) (degreeG : Nat) (g : Poly)
    (roots : List Z) : Z :=
  zMul (zPow leading degreeG)
    (listProd integerRing (roots.map (fun r => BEDC.Derived.PolynomialUp.polyEval r g)))

def RootListAnnihilates (f : Poly) : List Z -> Prop
  | [] => True
  | r :: roots => Zeq (BEDC.Derived.PolynomialUp.polyEval r f) zZero ∧
      RootListAnnihilates f roots

structure RootProductCertificate (degreeF degreeG : Nat) (f g : Poly)
    (leading : Z) where
  roots : List Z
  root_count : roots.length = degreeF
  roots_annihilate : RootListAnnihilates f roots
  resultant_matches_product :
    Zeq (resultant degreeF degreeG f g)
      (rootProductValue leading degreeG g roots)

theorem root_product_certificate_resultant_readback
    {degreeF degreeG : Nat} {f g : Poly} {leading : Z}
    (certificate : RootProductCertificate degreeF degreeG f g leading) :
    Zeq (resultant degreeF degreeG f g)
      (rootProductValue leading degreeG g certificate.roots) :=
  certificate.resultant_matches_product

def quadraticPolynomial (a b c : Z) : Poly :=
  [c, b, a]

def quadraticDerivative (a b : Z) : Poly :=
  [b, zMul zTwo a]

def quadraticDiscriminant (a b c : Z) : Z :=
  zSub (zSquare b) (zMul zFour (zMul a c))

def quadraticResultant (a b c : Z) : Z :=
  resultant 2 1 (quadraticPolynomial a b c) (quadraticDerivative a b)

structure QuadraticDiscriminantResultantCertificate (a b c : Z) where
  disc : Z
  disc_formula : Zeq disc (quadraticDiscriminant a b c)
  resultant_boundary : Zeq (quadraticResultant a b c) (zNeg (zMul a disc))

theorem quadratic_discriminant_from_resultant_certificate {a b c : Z}
    (certificate : QuadraticDiscriminantResultantCertificate a b c) :
    Zeq (quadraticResultant a b c)
      (zNeg (zMul a (quadraticDiscriminant a b c))) := by
  exact integerRing.trans certificate.resultant_boundary
    (integerRing.neg_congr
      (integerRing.mul_congr (integerRing.refl a) certificate.disc_formula))

theorem sylvester_quadratic_derivative_matrix (a b c : Z) :
    sylvesterMatrix 2 1 (quadraticPolynomial a b c) (quadraticDerivative a b) =
      [[c, b, a], [b, zMul zTwo a, zZero], [zZero, b, zMul zTwo a]] := by
  rfl

theorem quadratic_discriminant_formula (a b c : Z) :
    Zeq (quadraticDiscriminant a b c)
      (zSub (zMul b b) (zMul zFour (zMul a c))) :=
  integerRing.refl _

def monicZeroQuadratic : Poly :=
  quadraticPolynomial zOne zZero zZero

def monicZeroQuadraticDerivative : Poly :=
  quadraticDerivative zOne zZero

theorem monic_zero_quadratic_sylvester_matrix :
    sylvesterMatrix 2 1 monicZeroQuadratic monicZeroQuadraticDerivative =
      [[zZero, zZero, zOne], [zZero, zTwo, zZero], [zZero, zZero, zTwo]] := by
  rfl

theorem monic_zero_quadratic_discriminant_zero :
    Zeq (quadraticDiscriminant zOne zZero zZero) zZero := by
  unfold quadraticDiscriminant zSquare zFour zTwo zSub
  exact integerRing.trans (integerRing.sub_eq_add_neg
      (zMul zZero zZero)
      (zMul (zMul (zAdd zOne zOne) (zAdd zOne zOne))
        (zMul zOne zZero)))
    (integerRing.trans
      (integerRing.add_congr (integerRing.zero_mul zZero)
        (integerRing.neg_congr
          (integerRing.trans
            (integerRing.mul_congr (integerRing.refl _)
              (integerRing.mul_zero zOne))
            (integerRing.mul_zero _))))
      (integerRing.trans
        (integerRing.add_congr (integerRing.refl zZero) integerRing.neg_zero)
        (integerRing.add_zero zZero)))

end BEDC.Derived.ResultantUp

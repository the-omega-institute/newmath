import BEDC.Derived.ZeckendorfMobiusSieve

/-
Zeckendorf-window squarefree/Mobius-sieve finite certificate.

This file is not RH and does not claim Mertens or RH conclusions. It records
exact integer-polynomial identities tying the squarefree sieve for mu^2 to
finite Zeckendorf residue-transfer counts.
-/

namespace BEDC.Derived.ZeckendorfMobiusSquarefreeSieve

set_option maxRecDepth 20000

abbrev IPoly := BEDC.Derived.ZeckendorfMobiusSieve.IPoly

abbrev fib : Nat -> Nat :=
  BEDC.Derived.ZeckendorfMobiusSieve.fib

abbrev SQPoly : Nat -> IPoly :=
  BEDC.Derived.ZeckendorfMobiusSieve.SQ

abbrev muVal : Nat -> Int :=
  BEDC.Derived.ZeckendorfMobiusSieve.muVal

def trimPoly (p : IPoly) : IPoly :=
  BEDC.Derived.ZeckendorfMobiusSieve.trimTrailingZeros p

def addPolyRaw : IPoly -> IPoly -> IPoly
| [], q => q
| p, [] => p
| a :: as, b :: bs => (a + b) :: addPolyRaw as bs

def addPoly (p q : IPoly) : IPoly :=
  trimPoly (addPolyRaw p q)

def scalePolyRaw (c : Int) : IPoly -> IPoly
| [] => []
| a :: as => (c * a) :: scalePolyRaw c as

def scalePoly (c : Int) (p : IPoly) : IPoly :=
  trimPoly (scalePolyRaw c p)

def shiftByU : IPoly -> IPoly
| [] => []
| a :: as => 0 :: a :: as

def subOne (p : IPoly) : IPoly :=
  addPoly p [(-1 : Int)]

def residueKey (D r : Nat) : Nat :=
  if D == 0 then r else r % D

abbrev ResiduePoly := Nat × IPoly

def lookupResidue (key : Nat) : List ResiduePoly -> IPoly
| [] => []
| entry :: rest =>
    if entry.1 == key then entry.2 else lookupResidue key rest

def insertResidueAdd (key : Nat) (p : IPoly) : List ResiduePoly -> List ResiduePoly
| [] =>
    if BEDC.Derived.ZeckendorfMobiusSieve.allZero p then [] else [(key, p)]
| entry :: rest =>
    if entry.1 == key then
      let updated := addPoly entry.2 p
      if BEDC.Derived.ZeckendorfMobiusSieve.allZero updated then rest
      else (entry.1, updated) :: rest
    else
      entry :: insertResidueAdd key p rest

def addResidueMap : List ResiduePoly -> List ResiduePoly -> List ResiduePoly
| base, [] => base
| base, entry :: rest => addResidueMap (insertResidueAdd entry.1 entry.2 base) rest

def oddResidueMap (D i : Nat) : List ResiduePoly -> List ResiduePoly
| [] => []
| entry :: rest =>
    insertResidueAdd
      (residueKey D (entry.1 + fib (i + 2)))
      (shiftByU entry.2)
      (oddResidueMap D i rest)

abbrev TransferState := List ResiduePoly × List ResiduePoly

def transferStep (D i : Nat) (state : TransferState) : TransferState :=
  (addResidueMap state.1 state.2, oddResidueMap D i state.1)

def transferRun (D : Nat) : Nat -> Nat -> TransferState -> TransferState
| 0, _i, state => state
| fuel + 1, i, state => transferRun D fuel (i + 1) (transferStep D i state)

def residueTransferC (m D a : Nat) : IPoly :=
  let state := transferRun D m 0 ([(0, [1])], [])
  addPoly
    (lookupResidue (residueKey D a) state.1)
    (lookupResidue (residueKey D a) state.2)

def sieveRHSFrom (m d : Nat) : Nat -> IPoly
| 0 => []
| fuel + 1 =>
    addPoly
      (scalePoly (muVal d) (subOne (residueTransferC m (d * d) 0)))
      (sieveRHSFrom m (d + 1) fuel)

def sieveRHS (m : Nat) : IPoly :=
  let stop := fib (m + 2)
  sieveRHSFrom m 1 (stop - 1)

theorem squarefreePolynomial_m0 : SQPoly 0 = [] := by
  rfl

theorem squarefreePolynomial_m1 : SQPoly 1 = [0, 1] := by
  rfl

theorem squarefreePolynomial_m2 : SQPoly 2 = [0, 2] := by
  rfl

theorem squarefreePolynomial_m3 : SQPoly 3 = [0, 3] := by
  rfl

theorem squarefreePolynomial_m4 : SQPoly 4 = [0, 4, 2] := by
  rfl

theorem squarefreePolynomial_m5 : SQPoly 5 = [0, 4, 4] := by
  rfl

theorem squarefreePolynomial_m6 : SQPoly 6 = [0, 5, 6, 2] := by
  rfl

theorem squarefreePolynomial_m7 : SQPoly 7 = [0, 6, 10, 4, 1] := by
  rfl

theorem squarefreePolynomial_m8 : SQPoly 8 = [0, 7, 15, 7, 4] := by
  rfl

theorem squarefreeMobiusSieveTransfer_m0 : SQPoly 0 = sieveRHS 0 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m1 : SQPoly 1 = sieveRHS 1 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m2 : SQPoly 2 = sieveRHS 2 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m3 : SQPoly 3 = sieveRHS 3 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m4 : SQPoly 4 = sieveRHS 4 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m5 : SQPoly 5 = sieveRHS 5 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m6 : SQPoly 6 = sieveRHS 6 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m7 : SQPoly 7 = sieveRHS 7 := by
  rfl

theorem squarefreeMobiusSieveTransfer_m8 : SQPoly 8 = sieveRHS 8 := by
  rfl

/--
Finite Zeckendorf-window certificate for the squarefree Mobius-sieve transfer.
The window bound is explicit: the statement covers exactly `m = 0, ..., 8`.
-/
theorem squarefreeMobiusSieveTransfer_windowCertificate :
    SQPoly 0 = sieveRHS 0 ∧
    SQPoly 1 = sieveRHS 1 ∧
    SQPoly 2 = sieveRHS 2 ∧
    SQPoly 3 = sieveRHS 3 ∧
    SQPoly 4 = sieveRHS 4 ∧
    SQPoly 5 = sieveRHS 5 ∧
    SQPoly 6 = sieveRHS 6 ∧
    SQPoly 7 = sieveRHS 7 ∧
    SQPoly 8 = sieveRHS 8 := by
  constructor
  · exact squarefreeMobiusSieveTransfer_m0
  constructor
  · exact squarefreeMobiusSieveTransfer_m1
  constructor
  · exact squarefreeMobiusSieveTransfer_m2
  constructor
  · exact squarefreeMobiusSieveTransfer_m3
  constructor
  · exact squarefreeMobiusSieveTransfer_m4
  constructor
  · exact squarefreeMobiusSieveTransfer_m5
  constructor
  · exact squarefreeMobiusSieveTransfer_m6
  constructor
  · exact squarefreeMobiusSieveTransfer_m7
  · exact squarefreeMobiusSieveTransfer_m8

end BEDC.Derived.ZeckendorfMobiusSquarefreeSieve

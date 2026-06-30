import BEDC.Derived.HarmonicUp
import BEDC.Derived.GcdUp

namespace BEDC.Derived.HarmonicNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RationalUp
open BEDC.Derived.HarmonicUp
open BEDC.Derived.GcdUp

abbrev HarmonicRat : Type :=
  RatNum

def harmonicNumberTerm (k : Nat) : HarmonicRat :=
  oneOverNatSucc k

def harmonicNumber : Nat -> HarmonicRat :=
  harmonic

def harmonicNumberTerms : Nat -> List HarmonicRat :=
  harmonicTerms

def harmonicNumberSum : List HarmonicRat -> HarmonicRat :=
  ratListSum

theorem harmonicNumber_zero :
    RatEq (harmonicNumber 0) ratZero := by
  exact harmonic_zero

theorem harmonicNumber_succ (n : Nat) :
    RatEq (harmonicNumber (Nat.succ n))
      (ratAdd (harmonicNumber n) (harmonicNumberTerm n)) := by
  exact harmonic_succ n

theorem harmonicNumber_as_finite_sum (n : Nat) :
    harmonicNumber n = harmonicNumberSum (harmonicNumberTerms n) := by
  exact harmonic_as_sum n

def reciprocalNatSuccPower (k : Nat) : Nat -> HarmonicRat
  | 0 => ratOne
  | Nat.succ m => ratMul (reciprocalNatSuccPower k m) (harmonicNumberTerm k)

def generalizedHarmonicNumber (m : Nat) : Nat -> HarmonicRat
  | 0 => ratZero
  | Nat.succ n =>
      ratAdd (generalizedHarmonicNumber m n) (reciprocalNatSuccPower n m)

def generalizedHarmonicNumberTerms (m : Nat) : Nat -> List HarmonicRat
  | 0 => []
  | Nat.succ n => reciprocalNatSuccPower n m :: generalizedHarmonicNumberTerms m n

theorem reciprocalNatSuccPower_zero (k : Nat) :
    RatEq (reciprocalNatSuccPower k 0) ratOne := by
  exact RatEq_refl ratOne

theorem reciprocalNatSuccPower_succ (k m : Nat) :
    RatEq (reciprocalNatSuccPower k (Nat.succ m))
      (ratMul (reciprocalNatSuccPower k m) (harmonicNumberTerm k)) := by
  exact RatEq_refl _

theorem reciprocalNatSuccPower_one (k : Nat) :
    RatEq (reciprocalNatSuccPower k 1) (harmonicNumberTerm k) := by
  change RatEq (ratMul ratOne (harmonicNumberTerm k)) (harmonicNumberTerm k)
  exact ratOne_mul_left (harmonicNumberTerm k)

theorem generalizedHarmonicNumber_zero (m : Nat) :
    RatEq (generalizedHarmonicNumber m 0) ratZero := by
  exact RatEq_refl ratZero

theorem generalizedHarmonicNumber_succ (m n : Nat) :
    RatEq (generalizedHarmonicNumber m (Nat.succ n))
      (ratAdd (generalizedHarmonicNumber m n) (reciprocalNatSuccPower n m)) := by
  exact RatEq_refl _

theorem generalizedHarmonicNumber_as_finite_sum (m n : Nat) :
    generalizedHarmonicNumber m n =
      harmonicNumberSum (generalizedHarmonicNumberTerms m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change ratAdd (generalizedHarmonicNumber m n) (reciprocalNatSuccPower n m) =
        ratAdd (harmonicNumberSum (generalizedHarmonicNumberTerms m n))
          (reciprocalNatSuccPower n m)
      exact congrArg (fun h => ratAdd h (reciprocalNatSuccPower n m)) ih

theorem generalizedHarmonicNumber_order_one (n : Nat) :
    RatEq (generalizedHarmonicNumber 1 n) (harmonicNumber n) := by
  induction n with
  | zero =>
      exact RatEq_refl ratZero
  | succ n ih =>
      exact RatEq_trans
        (generalizedHarmonicNumber 1 (Nat.succ n))
        (ratAdd (harmonicNumber n) (harmonicNumberTerm n))
        (harmonicNumber (Nat.succ n))
        (ratAdd_respects ih (reciprocalNatSuccPower_one n))
        (RatEq_symm (harmonicNumber_succ n))

def RatIntegerWitness (x : HarmonicRat) : Prop :=
  Exists (fun z : BEDC.Derived.PrimeUp.IntegerUp => RatEq x (intToRat z))

def HarmonicNumberNonintegerAt (n : Nat) : Prop :=
  RatIntegerWitness (harmonicNumber n) -> False

structure HarmonicNumberNonintegerCertificate (n : Nat) where
  startsAtTwo : 2 <= n
  notInteger : HarmonicNumberNonintegerAt n

theorem harmonicNumberNonintegerCertificate_readback {n : Nat}
    (cert : HarmonicNumberNonintegerCertificate n) :
    2 <= n /\ HarmonicNumberNonintegerAt n :=
  And.intro cert.startsAtTwo cert.notInteger

structure WolstenholmeStyleNonintegerData (n : Nat) where
  obstructionPrime : BHist
  denominatorWindow : BHist
  obstructionPrime_is_prime : BEDC.Derived.PrimeUp.NatPrime obstructionPrime
  obstructionPrimeUnary : UnaryHistory obstructionPrime
  denominatorWindowUnary : UnaryHistory denominatorWindow
  coprimeWindow : NatGcd obstructionPrime denominatorWindow NatOne
  notInteger : HarmonicNumberNonintegerAt n

theorem wolstenholmeStyleNonintegerData_readback {n : Nat}
    (data : WolstenholmeStyleNonintegerData n) :
    HarmonicNumberNonintegerAt n :=
  data.notInteger

theorem wolstenholmeStyleNonintegerData_prime_readback {n : Nat}
    (data : WolstenholmeStyleNonintegerData n) :
    BEDC.Derived.PrimeUp.NatPrime data.obstructionPrime :=
  data.obstructionPrime_is_prime

structure FormalPsiShiftBridge where
  psi : Nat -> HarmonicRat
  eulerConstantSymbol : HarmonicRat
  psi_shift_relation :
    forall n : Nat,
      RatEq (ratAdd (psi (Nat.succ n)) eulerConstantSymbol) (harmonicNumber n)

def formalPsiFromHarmonic : Nat -> HarmonicRat
  | 0 => ratZero
  | Nat.succ n => harmonicNumber n

def harmonicNumberFormalPsiBridge : FormalPsiShiftBridge where
  psi := formalPsiFromHarmonic
  eulerConstantSymbol := ratZero
  psi_shift_relation := by
    intro n
    change RatEq (ratAdd (harmonicNumber n) ratZero) (harmonicNumber n)
    exact ratAdd_zero_right (harmonicNumber n)

theorem formalPsiShiftBridge_readback (bridge : FormalPsiShiftBridge) (n : Nat) :
    RatEq (ratAdd (bridge.psi (Nat.succ n)) bridge.eulerConstantSymbol)
      (harmonicNumber n) :=
  bridge.psi_shift_relation n

theorem harmonicNumberFormalPsiBridge_relation (n : Nat) :
    RatEq
      (ratAdd (harmonicNumberFormalPsiBridge.psi (Nat.succ n))
        harmonicNumberFormalPsiBridge.eulerConstantSymbol)
      (harmonicNumber n) :=
  formalPsiShiftBridge_readback harmonicNumberFormalPsiBridge n

theorem harmonicNumberUp_constructive_export (m n : Nat) :
    RatEq (harmonicNumber (Nat.succ n))
        (ratAdd (harmonicNumber n) (harmonicNumberTerm n)) /\
      RatEq (generalizedHarmonicNumber m (Nat.succ n))
        (ratAdd (generalizedHarmonicNumber m n) (reciprocalNatSuccPower n m)) /\
        RatEq (generalizedHarmonicNumber 1 n) (harmonicNumber n) /\
          RatEq
            (ratAdd (harmonicNumberFormalPsiBridge.psi (Nat.succ n))
              harmonicNumberFormalPsiBridge.eulerConstantSymbol)
            (harmonicNumber n) := by
  exact And.intro (harmonicNumber_succ n)
    (And.intro (generalizedHarmonicNumber_succ m n)
      (And.intro (generalizedHarmonicNumber_order_one n)
        (harmonicNumberFormalPsiBridge_relation n)))

end BEDC.Derived.HarmonicNumberUp

import BEDC.Derived.GcdUp
import BEDC.Derived.MobiusInversionUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.RamanujanSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.ZModUp

abbrev IntegerValue := IntegerUp

abbrev RamanujanRootEvaluator (q : BHist) :=
  ZMod q -> BHist -> IntegerValue

def primitiveResidue {q : BHist} (a : ZMod q) : Prop :=
  NatGcd a.val q NatOne

def PrimitiveResidueList (q : BHist) (residues : List (ZMod q)) : Prop :=
  forall a : ZMod q, a ∈ residues -> primitiveResidue a

def ramanujanRootTerm {q : BHist} (root : RamanujanRootEvaluator q)
    (a : ZMod q) (n : BHist) : IntegerValue :=
  root a n

def ramanujanRootSum (q : BHist) (root : RamanujanRootEvaluator q)
    (residues : List (ZMod q)) (n : BHist) : IntegerValue :=
  integerUpListSum (residues.map (fun a => ramanujanRootTerm root a n))

def removeOneFactor (p : BHist) : List BHist -> List BHist
  | [] => []
  | q :: qs => if p = q then qs else q :: removeOneFactor p qs

def factorListSubmultiset : List BHist -> List BHist -> Bool
  | [], _ => true
  | p :: ps, qs =>
      if listContainsPrime p qs then
        factorListSubmultiset ps (removeOneFactor p qs)
      else false

def commonDivisorFactorSplits (n q : List BHist) :
    List (List BHist × List BHist) :=
  match n with
  | [] => [([], q)]
  | _ :: _ =>
      (divisorFactorSplits q).filter
        (fun split => factorListSubmultiset split.1 n)

def factorListProductNat : List BHist -> Nat
  | [] => 1
  | p :: ps => bwordLength p * factorListProductNat ps

def factorListProductInteger (entries : List BHist) : IntegerValue :=
  intOfNat (natToUnary (factorListProductNat entries))
    (natToUnary_unary (factorListProductNat entries))

def kluyverTerm (split : List BHist × List BHist) : IntegerValue :=
  IntMul
    (factorListProductInteger split.1)
    (mobiusFactorsIntegerUp split.2)

def kluyverDivisorSum (n q : List BHist) : IntegerValue :=
  integerUpListSum
    ((commonDivisorFactorSplits n q).map kluyverTerm)

def ramanujanSum (n q : List BHist) : IntegerValue :=
  kluyverDivisorSum n q

def RamanujanKluyverFormula (q : List BHist) (value : ArithmeticFunction) : Prop :=
  forall entries : List BHist,
    IntEq (value entries) (kluyverDivisorSum entries q)

def RamanujanRootSumRealizesKluyver (q : BHist) (root : RamanujanRootEvaluator q)
    (residues : List (ZMod q)) (nEntries qEntries : List BHist) : Prop :=
  PrimitiveResidueList q residues ∧
    IntEq (ramanujanRootSum q root residues (factorListProductFn nEntries))
      (kluyverDivisorSum nEntries qEntries)

private theorem integerUpListSum_single (x : IntegerValue) :
    IntEq (integerUpListSum [x]) x := by
  change IntEq (IntAdd x intZero) x
  exact BEDC.Derived.RationalUp.IntAdd_zero x

private theorem factorListProductInteger_nil :
    IntEq (factorListProductInteger []) intOne := by
  change IntEq (intOfNat NatOne (natToUnary_unary 1)) intOne
  exact IntEq_refl intOne

private theorem intMul_factorListProductInteger_nil_left (x : IntegerValue) :
    IntEq (IntMul (factorListProductInteger []) x) x := by
  exact BEDC.Derived.RationalUp.IntEq_trans
    (BEDC.Derived.RationalUp.IntMul_respects
      factorListProductInteger_nil (IntEq_refl x))
    (BEDC.Derived.RationalUp.IntMul_one_left x)

theorem factorListProductNat_nil :
    factorListProductNat ([] : List BHist) = 1 := by
  rfl

private theorem kluyverTerm_nil_left (q : List BHist) :
    IntEq (kluyverTerm ([], q)) (mobiusFactorsIntegerUp q) := by
  unfold kluyverTerm
  change IntEq
    (IntMul (factorListProductInteger [])
      (mobiusFactorsIntegerUp q))
    (mobiusFactorsIntegerUp q)
  exact intMul_factorListProductInteger_nil_left (mobiusFactorsIntegerUp q)

theorem kluyverDivisorSum_unit :
    IntEq (kluyverDivisorSum [] q) (mobiusFactorsIntegerUp q) := by
  unfold kluyverDivisorSum commonDivisorFactorSplits
  change IntEq (integerUpListSum [kluyverTerm ([], q)])
    (mobiusFactorsIntegerUp q)
  exact IntEq_trans (integerUpListSum_single (kluyverTerm ([], q)))
    (kluyverTerm_nil_left q)

theorem ramanujanSum_kluyver_formula (n q : List BHist) :
    IntEq (ramanujanSum n q) (kluyverDivisorSum n q) := by
  exact IntEq_refl (kluyverDivisorSum n q)

theorem ramanujanSum_one_eq_mobius (q : List BHist) :
    IntEq (ramanujanSum [] q) (mobiusFactorsIntegerUp q) := by
  exact kluyverDivisorSum_unit (q := q)

theorem ramanujanSum_root_bridge_scope
    (q : BHist) (root : RamanujanRootEvaluator q)
    (residues : List (ZMod q)) (nEntries qEntries : List BHist) :
    RamanujanRootSumRealizesKluyver q root residues nEntries qEntries ->
      IntEq (ramanujanRootSum q root residues (factorListProductFn nEntries))
        (ramanujanSum nEntries qEntries) := by
  intro bridge
  exact bridge.right

end BEDC.Derived.RamanujanSumUp

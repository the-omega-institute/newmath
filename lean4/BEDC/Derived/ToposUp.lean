import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ToposUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ToposFiniteCarrier [AskSetup] [PackageSetup]
    (category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
    UnaryHistory exponential ∧ UnaryHistory subobjectClassifier ∧
      Cont category sheaf comparison ∧ Cont finiteLimit exponential ledger ∧
        Cont ledger subobjectClassifier provenance ∧ Cont comparison provenance endpoint ∧
          PkgSig bundle endpoint pkg

theorem ToposFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont category sheaf comparison ∧ Cont finiteLimit exponential ledger ∧
          Cont ledger subobjectClassifier provenance ∧ Cont comparison provenance endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrierData
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
            comparison ledger provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrierData (hsame_refl endpoint))
  obtain ⟨_categoryUnary, _sheafUnary, _finiteLimitUnary, _exponentialUnary,
    _subobjectClassifierUnary, comparisonRow, ledgerRow, provenanceRow, endpointRow,
    pkgSig⟩ := carrierData
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro comparisonRow
      (And.intro ledgerRow (And.intro provenanceRow (And.intro endpointRow pkgSig))))

end BEDC.Derived.ToposUp

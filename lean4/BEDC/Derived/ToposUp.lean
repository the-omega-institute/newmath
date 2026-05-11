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

def ToposSubobjectClassifierLedger [AskSetup] [PackageSetup]
    (category sheaf finiteLimit exponential subobject contRows provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
    UnaryHistory exponential ∧ UnaryHistory subobject ∧ UnaryHistory endpoint ∧
      Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
        Cont subobject contRows endpoint ∧ PkgSig probe provenance pkg

theorem ToposSubobjectClassifierLedger_exactness [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject contRows provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
        provenance endpoint probe pkg ->
      UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
        UnaryHistory exponential ∧ UnaryHistory subobject ∧ UnaryHistory endpoint ∧
          Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
            Cont subobject contRows endpoint ∧ PkgSig probe provenance pkg := by
  intro ledger
  have categoryUnary : UnaryHistory category :=
    ledger.left
  have sheafUnary : UnaryHistory sheaf :=
    ledger.right.left
  have finiteLimitUnary : UnaryHistory finiteLimit :=
    unary_cont_closed categoryUnary sheafUnary ledger.right.right.right.right.right.right.left
  have exponentialUnary : UnaryHistory exponential :=
    ledger.right.right.right.left
  have subobjectUnary : UnaryHistory subobject :=
    unary_cont_closed finiteLimitUnary exponentialUnary
      ledger.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    ledger.right.right.right.right.right.left
  have categorySheafRow : Cont category sheaf finiteLimit :=
    ledger.right.right.right.right.right.right.left
  have finiteExponentialRow : Cont finiteLimit exponential subobject :=
    ledger.right.right.right.right.right.right.right.left
  have subobjectEndpointRow : Cont subobject contRows endpoint :=
    ledger.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig probe provenance pkg :=
    ledger.right.right.right.right.right.right.right.right.right
  exact And.intro categoryUnary
    (And.intro sheafUnary
      (And.intro finiteLimitUnary
        (And.intro exponentialUnary
          (And.intro subobjectUnary
            (And.intro endpointUnary
              (And.intro categorySheafRow
                (And.intro finiteExponentialRow (And.intro subobjectEndpointRow pkgSig))))))))

theorem ToposFiniteCarrier_finite_limit_exponential_scope [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      UnaryHistory finiteLimit ∧ UnaryHistory exponential ∧ UnaryHistory subobjectClassifier ∧
        Cont finiteLimit exponential ledger ∧ Cont ledger subobjectClassifier provenance ∧
          Cont comparison provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrierData
  have finiteLimitUnary : UnaryHistory finiteLimit := carrierData.right.right.left
  have exponentialUnary : UnaryHistory exponential := carrierData.right.right.right.left
  have subobjectClassifierUnary : UnaryHistory subobjectClassifier :=
    carrierData.right.right.right.right.left
  have ledgerRow : Cont finiteLimit exponential ledger :=
    carrierData.right.right.right.right.right.right.left
  have provenanceRow : Cont ledger subobjectClassifier provenance :=
    carrierData.right.right.right.right.right.right.right.left
  have endpointRow : Cont comparison provenance endpoint :=
    carrierData.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrierData.right.right.right.right.right.right.right.right.right
  exact
    ⟨finiteLimitUnary, exponentialUnary, subobjectClassifierUnary, ledgerRow, provenanceRow,
      endpointRow, pkgSig⟩

end BEDC.Derived.ToposUp

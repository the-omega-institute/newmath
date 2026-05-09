import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CStarAlgUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CStarAlgCarrierRow [AskSetup] [PackageSetup]
    (banach ring involution normSquare transport ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) (h : BHist) : Prop :=
  hsame h provenance ∧ Cont banach ring ledger ∧ Cont involution normSquare transport ∧
    hsame transport (append involution normSquare) ∧ PkgSig bundle provenance pkg

def CStarAlgCertificateSurface [AskSetup] [PackageSetup]
    (banach ring involution normSquare transport ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance bundle pkg
      provenance ∧
    Cont banach ring ledger ∧ PkgSig bundle provenance pkg

theorem CStarAlgCertificateSurface_namecert_obligation [AskSetup] [PackageSetup]
    {banach ring involution normSquare transport ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CStarAlgCertificateSurface banach ring involution normSquare transport ledger provenance
        bundle pkg ->
      SemanticNameCert
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (fun h k : BHist =>
            CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
              bundle pkg h ∧
            CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
              bundle pkg k ∧
            hsame h k) ∧
        Cont banach ring ledger ∧ PkgSig bundle provenance pkg := by
  intro surface
  have sourceRow :
      CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
        bundle pkg provenance :=
    surface.left
  have banachRingLedger : Cont banach ring ledger :=
    surface.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    surface.right.right
  have cert :
      SemanticNameCert
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
            bundle pkg)
          (fun h k : BHist =>
            CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
              bundle pkg h ∧
            CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
              bundle pkg k ∧
            hsame h k) := {
    core := {
      carrier_inhabited := Exists.intro provenance sourceRow
      equiv_refl := by
        intro row carrierRow
        exact And.intro carrierRow (And.intro carrierRow (hsame_refl row))
      equiv_symm := by
        intro row row' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro row row' row'' leftClassified rightClassified
        exact And.intro leftClassified.left
          (And.intro rightClassified.right.left
            (hsame_trans leftClassified.right.right rightClassified.right.right))
      carrier_respects_equiv := by
        intro row row' classified _carrierRow
        exact classified.right.left
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }
  exact And.intro cert (And.intro banachRingLedger provenancePkg)

theorem CStarAlgCertificateSurface_gelfand_vonneumann_consumer_boundary
    [AskSetup] [PackageSetup]
    {banach ring involution normSquare transport ledger provenance consumer out : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CStarAlgCertificateSurface banach ring involution normSquare transport ledger provenance
        bundle pkg ->
      Cont provenance consumer out ->
        CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance bundle
            pkg provenance ∧
          Cont banach ring ledger ∧ Cont provenance consumer out ∧
            hsame out (append provenance consumer) ∧ PkgSig bundle provenance pkg := by
  intro surface consumerRow
  have carrierRow :
      CStarAlgCarrierRow banach ring involution normSquare transport ledger provenance
        bundle pkg provenance :=
    surface.left
  have banachRingLedger : Cont banach ring ledger :=
    surface.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    surface.right.right
  exact And.intro carrierRow
    (And.intro banachRingLedger
      (And.intro consumerRow (And.intro consumerRow provenancePkg)))

end BEDC.Derived.CStarAlgUp

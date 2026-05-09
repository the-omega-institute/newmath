import BEDC.Derived.BanachUp
import BEDC.Derived.RingUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CStarAlgUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.RingUp

def CstaralgebraBHistCarrier [AskSetup] [PackageSetup]
    (banach ring multiplication involution normSquare provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory multiplication ∧
    UnaryHistory involution ∧ UnaryHistory normSquare ∧ UnaryHistory provenance ∧
      Cont banach ring multiplication ∧ Cont multiplication involution normSquare ∧
        Cont normSquare provenance ledger ∧ PkgSig bundle ledger pkg

theorem CstaralgebraBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {banach ring multiplication involution normSquare provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CstaralgebraBHistCarrier banach ring multiplication involution normSquare provenance
      ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
        hsame ∧
        UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory multiplication ∧
          UnaryHistory involution ∧ UnaryHistory normSquare ∧ UnaryHistory ledger ∧
            Cont banach ring multiplication ∧ Cont multiplication involution normSquare ∧
              Cont normSquare provenance ledger ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.right.right.left
      carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  exact And.intro
    {
      core := {
        carrier_inhabited := Exists.intro ledger (hsame_refl ledger)
        equiv_refl := by
          intro h _source
          exact hsame_refl h
        equiv_symm := by
          intro h k same
          exact hsame_symm same
        equiv_trans := by
          intro h k r sameHK sameKR
          exact hsame_trans sameHK sameKR
        carrier_respects_equiv := by
          intro h k same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro carrier.right.right.right.right.left
              (And.intro unaryLedger
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.right.right.left
                      carrier.right.right.right.right.right.right.right.right.right)))))))))

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

def CStarAlgBHistCarrier
    (banach ring involution norm provenance ledger endpoint : BHist) : Prop :=
  BanachSingletonCarrier banach ∧ RingSingletonCarrier ring ∧ UnaryHistory involution ∧
    UnaryHistory norm ∧ UnaryHistory provenance ∧ Cont ring involution ledger ∧
      Cont provenance ledger endpoint

theorem CStarAlgBHistCarrier_namecert_obligation_surface
    {banach ring involution norm provenance ledger endpoint : BHist} :
    CStarAlgBHistCarrier banach ring involution norm provenance ledger endpoint ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) hsame ∧
        BanachSingletonCarrier banach ∧ RingSingletonCarrier ring ∧ UnaryHistory involution ∧
          UnaryHistory norm ∧ UnaryHistory ledger ∧ hsame ledger (append ring involution) ∧
            hsame endpoint (append provenance ledger) := by
  intro carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed
      (unary_transport unary_empty (hsame_symm carrier.right.left))
      carrier.right.right.left
      carrier.right.right.right.right.right.left
  have endpointSelf : hsame endpoint endpoint := hsame_refl endpoint
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSelf
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK source
        exact hsame_trans (hsame_symm sameHK) source
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro ledgerUnary
              (And.intro carrier.right.right.right.right.right.left
                carrier.right.right.right.right.right.right))))))

end BEDC.Derived.CStarAlgUp

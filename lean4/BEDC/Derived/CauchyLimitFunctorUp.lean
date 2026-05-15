import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLimitFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyLimitFunctorCarrier [AskSetup] [PackageSetup]
    (sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceSeal ∧ UnaryHistory targetSeal ∧ UnaryHistory transportMap ∧
    UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧ UnaryHistory readback ∧
      UnaryHistory tolerance ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
        UnaryHistory hsameRows ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
          UnaryHistory nameCert ∧ UnaryHistory carrierEndpoint ∧
            Cont sourceSeal transportMap targetSeal ∧
              Cont sourceWindow targetWindow readback ∧
                Cont readback tolerance classifier ∧ Cont classifier endpoint carrierEndpoint ∧
                  Cont hsameRows routes provenance ∧ PkgSig bundle carrierEndpoint pkg

theorem CauchyLimitFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyLimitFunctorUp

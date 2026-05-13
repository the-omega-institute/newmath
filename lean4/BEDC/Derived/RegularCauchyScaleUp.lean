import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyScaleCarrier [AskSetup] [PackageSetup]
    (scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
    UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
      UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
        UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory namecert ∧ UnaryHistory endpoint ∧
            Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
              Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                Cont scaledEndpoint budget readback ∧ Cont readback route provenance ∧
                  Cont provenance namecert endpoint ∧ hsame sameRows (append scalar source) ∧
                    PkgSig bundle endpoint pkg

theorem RegularCauchyScaleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.RegularCauchyScaleUp

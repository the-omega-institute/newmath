import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergenceBHistCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector ledger ∧
        Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ModulusOfConvergenceBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceBHistCarrier precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
          UnaryHistory schedule ∧ UnaryHistory witness ∧ Cont precision selector ledger ∧
            Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary,
    _ledgerUnary, _provenanceUnary, precisionSelectorRoute, endpointRoute, pkgRoute⟩ := carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint) hsame :=
    {
      core := {
        carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact hsame_trans (hsame_symm sameRows) source
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact
    ⟨cert, precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary,
      precisionSelectorRoute, endpointRoute, pkgRoute⟩

end BEDC.Derived.ModulusOfConvergenceUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformLimitCarrier [AskSetup] [PackageSetup]
    (family modulus tail regularHandoff «seal» endpoint sameRows route provenance namecert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧
    UnaryHistory regularHandoff ∧ UnaryHistory «seal» ∧ UnaryHistory endpoint ∧
      UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory namecert ∧ Cont family modulus tail ∧ Cont tail regularHandoff «seal» ∧
          Cont regularHandoff «seal» endpoint ∧ Cont endpoint namecert provenance ∧
            hsame sameRows (append family modulus) ∧ PkgSig bundle endpoint pkg

theorem UniformLimitCarrier_seal_factorization [AskSetup] [PackageSetup]
    {family modulus tail regularHandoff «seal» endpoint sameRows route provenance namecert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformLimitCarrier family modulus tail regularHandoff «seal» endpoint sameRows route
        provenance namecert bundle pkg ->
      Cont regularHandoff «seal» endpoint ->
        Cont endpoint namecert publicRead ->
          UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧
            UnaryHistory regularHandoff ∧ UnaryHistory «seal» ∧ UnaryHistory endpoint ∧
              UnaryHistory publicRead ∧ Cont family modulus tail ∧
                Cont tail regularHandoff «seal» ∧ Cont regularHandoff «seal» endpoint ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier regularSealEndpoint endpointNamePublicRead
  obtain ⟨familyUnary, modulusUnary, tailUnary, regularHandoffUnary, sealUnary,
    endpointUnary, _sameRowsUnary, _routeUnary, _provenanceUnary, namecertUnary,
    familyModulusTail, tailRegularSeal, _carrierRegularSealEndpoint,
    _endpointNameProvenance, _sameRows, endpointPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary namecertUnary endpointNamePublicRead
  exact
    ⟨familyUnary, modulusUnary, tailUnary, regularHandoffUnary, sealUnary, endpointUnary,
      publicReadUnary, familyModulusTail, tailRegularSeal, regularSealEndpoint, endpointPkg⟩

theorem UniformLimitCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family modulus tail regularHandoff sealRow endpoint sameRows route provenance namecert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformLimitCarrier family modulus tail regularHandoff sealRow endpoint sameRows route
        provenance namecert bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
        (fun row : BHist => Cont regularHandoff sealRow row ∧ Cont family modulus tail)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg) hsame := by
  intro carrier
  obtain ⟨familyUnary, modulusUnary, _tailUnary, regularHandoffUnary, sealUnary, endpointUnary,
    _sameRowsUnary, _routeUnary, _provenanceUnary, _namecertUnary, familyModulusTail,
    _tailRegularSeal, regularSealEndpoint, _endpointNameProvenance, _sameRows,
    endpointPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro (hsame_refl endpoint) endpointUnary)
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
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact And.intro regularSealEndpoint familyModulusTail
    ledger_sound := by
      intro _row source
      cases source.left
      exact And.intro (hsame_refl endpoint) endpointPkg
  }

end BEDC.Derived.UniformLimitUp

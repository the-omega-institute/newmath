import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem AuthorizedGeneratorRecursorDownstreamNameCertPackage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N downstream boundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A downstream ->
        Cont downstream G boundary ->
          Cont boundary N terminal ->
            PkgSig bundle terminal pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                    hsame row terminal)
                (fun _row : BHist =>
                  Cont I E M ∧ Cont M B D ∧ Cont D O A ∧ Cont O A downstream ∧
                    Cont downstream G boundary ∧ Cont boundary N terminal ∧
                      hsame H (append A C))
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ PkgSig bundle terminal pkg ∧ hsame row terminal)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputDownstream downstreamBoundary boundaryTerminal terminalPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, carrierIEM, carrierMBD, carrierDOA, sameTransport, provenancePkg⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminal
          (And.intro
            ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
              unaryP, unaryG, unaryN, carrierIEM, carrierMBD, carrierDOA, sameTransport,
              provenancePkg⟩
            (hsame_refl terminal))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨carrierIEM, carrierMBD, carrierDOA, outputDownstream, downstreamBoundary,
          boundaryTerminal, sameTransport⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, terminalPkg, source.right⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp

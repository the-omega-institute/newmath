import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VermaModuleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem VermaModuleHighestWeightLedger_boundary [AskSetup] [PackageSetup]
    {lie roots highest borel generator provenance endpoint lowering readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lie -> UnaryHistory roots -> UnaryHistory highest -> UnaryHistory lowering ->
      Cont lie roots highest -> Cont highest borel generator ->
        Cont generator provenance endpoint -> Cont highest lowering readback ->
          Cont readback provenance endpoint -> PkgSig bundle endpoint pkg ->
            UnaryHistory readback ∧ Cont highest lowering readback ∧
              Cont readback provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro _lieUnary _rootsUnary highestUnary loweringUnary _lieRootsRow _borelRow
    _generatorEndpointRow loweringRow readbackEndpointRow pkgSig
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed highestUnary loweringUnary loweringRow
  exact And.intro readbackUnary
    (And.intro loweringRow (And.intro readbackEndpointRow pkgSig))

theorem VermaModuleFiniteCarrier_obligation_surface
    {lie root highest action generator provenance endpoint : BHist} :
    UnaryHistory lie ->
      UnaryHistory root ->
        UnaryHistory action ->
          UnaryHistory provenance ->
            Cont lie root highest ->
              Cont highest action generator ->
                Cont generator provenance endpoint ->
                  UnaryHistory highest ∧ UnaryHistory generator ∧ UnaryHistory endpoint ∧
                    hsame highest (append lie root) ∧
                      hsame generator (append highest action) ∧
                        hsame endpoint (append generator provenance) := by
  intro lieUnary rootUnary actionUnary provenanceUnary lieRootHighest highestActionGenerator
  intro generatorProvenanceEndpoint
  have highestUnary : UnaryHistory highest :=
    unary_cont_closed lieUnary rootUnary lieRootHighest
  have generatorUnary : UnaryHistory generator :=
    unary_cont_closed highestUnary actionUnary highestActionGenerator
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed generatorUnary provenanceUnary generatorProvenanceEndpoint
  exact And.intro highestUnary
    (And.intro generatorUnary
      (And.intro endpointUnary
        (And.intro lieRootHighest
          (And.intro highestActionGenerator generatorProvenanceEndpoint))))

def VermaModuleFiniteCarrier [AskSetup] [PackageSetup]
    (lie root highest borel generator lowering contRows provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lie ∧ UnaryHistory root ∧ UnaryHistory highest ∧
    UnaryHistory borel ∧ UnaryHistory generator ∧ UnaryHistory lowering ∧
      UnaryHistory contRows ∧ UnaryHistory provenance ∧ Cont lie root highest ∧
        Cont highest borel generator ∧ Cont generator lowering contRows ∧
          PkgSig bundle endpoint pkg

theorem VermaModuleFiniteCarrier_highest_weight_ledger [AskSetup] [PackageSetup]
    {lie root highest borel generator lowering contRows provenance endpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VermaModuleFiniteCarrier lie root highest borel generator lowering contRows provenance
        endpoint bundle pkg ->
      Cont highest lowering ledger ->
        UnaryHistory ledger ∧ Cont lie root highest ∧ Cont highest borel generator ∧
          Cont generator lowering contRows ∧ Cont highest lowering ledger ∧
            PkgSig bundle endpoint pkg := by
  intro carrier ledgerRow
  obtain ⟨_lieUnary, _rootUnary, highestUnary, _borelUnary, _generatorUnary,
    loweringUnary, _contRowsUnary, _provenanceUnary, lieRootRow, highestBorelRow,
    generatorLoweringRow, packageRow⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed highestUnary loweringUnary ledgerRow
  exact And.intro ledgerUnary
    (And.intro lieRootRow
      (And.intro highestBorelRow
        (And.intro generatorLoweringRow (And.intro ledgerRow packageRow))))

theorem VermaModuleFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {lie root highest borel generator lowering contRows provenance endpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VermaModuleFiniteCarrier lie root highest borel generator lowering contRows provenance
        endpoint bundle pkg ->
      Cont highest lowering ledger ->
        SemanticNameCert (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger) hsame ∧
          UnaryHistory ledger ∧ Cont lie root highest ∧ Cont highest borel generator ∧
            Cont generator lowering contRows ∧ Cont highest lowering ledger ∧
              PkgSig bundle endpoint pkg := by
  intro carrier ledgerRow
  rcases carrier with
    ⟨_lieUnary, _rootUnary, highestUnary, _borelUnary, _generatorUnary, loweringUnary,
      _contRowsUnary, _provenanceUnary, lieRootRow, highestBorelRow, generatorLoweringRow,
      packageRow⟩
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed highestUnary loweringUnary ledgerRow
  have cert :
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger (hsame_refl ledger)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, ledgerUnary, lieRootRow, highestBorelRow, generatorLoweringRow, ledgerRow,
    packageRow⟩

end BEDC.Derived.VermaModuleUp

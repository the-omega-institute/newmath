import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VermaModuleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

end BEDC.Derived.VermaModuleUp

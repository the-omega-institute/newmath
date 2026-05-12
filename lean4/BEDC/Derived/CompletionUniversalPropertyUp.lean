import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionUniversalPropertyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionUniversalPropertyPacket [AskSetup] [PackageSetup]
    (completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory completion ∧ UnaryHistory diagonal ∧ UnaryHistory regular ∧
    UnaryHistory realSeal ∧ UnaryHistory nameRow ∧
      Cont completion diagonal extensionLedger ∧ Cont regular realSeal denseMap ∧
        Cont extensionLedger uniquenessLedger provenance ∧ PkgSig bundle provenance pkg

theorem CompletionUniversalPropertyPacket_extension_obligations [AskSetup] [PackageSetup]
    {completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
        extensionLedger uniquenessLedger provenance nameRow bundle pkg ->
      Cont extensionLedger nameRow exportRow ->
        PkgSig bundle exportRow pkg ->
          UnaryHistory completion ∧ UnaryHistory diagonal ∧ UnaryHistory regular ∧
            UnaryHistory realSeal ∧ UnaryHistory denseMap ∧ UnaryHistory extensionLedger ∧
              UnaryHistory exportRow ∧ Cont completion diagonal extensionLedger ∧
                Cont regular realSeal denseMap ∧ Cont extensionLedger nameRow exportRow ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle exportRow pkg := by
  intro packet exportRoute exportPkg
  obtain ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, nameRowUnary,
    extensionRoute, denseRoute, _provenanceRoute, provenancePkg⟩ := packet
  have extensionUnary : UnaryHistory extensionLedger :=
    unary_cont_closed completionUnary diagonalUnary extensionRoute
  have denseUnary : UnaryHistory denseMap :=
    unary_cont_closed regularUnary realSealUnary denseRoute
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed extensionUnary nameRowUnary exportRoute
  exact
    ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, denseUnary,
      extensionUnary, exportUnary, extensionRoute, denseRoute, exportRoute, provenancePkg,
      exportPkg⟩

end BEDC.Derived.CompletionUniversalPropertyUp

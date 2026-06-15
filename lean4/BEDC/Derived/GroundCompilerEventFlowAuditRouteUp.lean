import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GroundCompilerEventFlowAuditRouteCarrier [AskSetup] [PackageSetup]
    (eventFlow channel lossless recognizer gate boundary transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory eventFlow ∧ UnaryHistory channel ∧ UnaryHistory lossless ∧
    UnaryHistory recognizer ∧ UnaryHistory gate ∧ UnaryHistory boundary ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont eventFlow channel lossless ∧
          Cont lossless recognizer gate ∧ Cont gate boundary route ∧
            Cont route provenance localName ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem GroundCompilerEventFlowAuditRouteNamecertObligations [AskSetup] [PackageSetup]
    {eventFlow channel lossless recognizer gate boundary transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroundCompilerEventFlowAuditRouteCarrier eventFlow channel lossless recognizer gate boundary
        transport route provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row channel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row gate ∨ hsame row boundary ∨
                hsame row localName)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont route provenance localName)
          hsame ∧
        UnaryHistory eventFlow ∧ UnaryHistory channel ∧ UnaryHistory lossless ∧
          UnaryHistory recognizer ∧ UnaryHistory gate ∧ UnaryHistory boundary ∧
            UnaryHistory localName := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨eventFlowUnary, channelUnary, losslessUnary, recognizerUnary, gateUnary,
    boundaryUnary, _transportUnary, _routeUnary, _provenanceUnary, localNameUnary,
    _eventFlowChannelLossless, _losslessRecognizerGate, _gateBoundaryRoute,
    routeProvenanceLocalName, _provenancePkg, localNamePkg⟩ := carrier
  have sourceLocalName :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        localName := by
    exact ⟨hsame_refl localName, localNameUnary, localNamePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row eventFlow ∨ hsame row channel ∨ hsame row lossless ∨
              hsame row recognizer ∨ hsame row gate ∨ hsame row boundary ∨
                hsame row localName)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont route provenance localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
        cases sameRows
        exact
          ⟨source.left, source.right.left, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, routeProvenanceLocalName⟩
  }
  exact
    ⟨cert, eventFlowUnary, channelUnary, losslessUnary, recognizerUnary, gateUnary,
      boundaryUnary, localNameUnary⟩

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

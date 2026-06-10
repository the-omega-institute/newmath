import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionObligationRouting [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont readback sealRow routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                  hsame row readback ∨ hsame row sealRow ∨ hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont readback sealRow routeRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier route routePkg
  obtain ⟨_apartnessUnary, _separationUnary, _completionUnary, _streamUnary,
    readbackUnary, _toleranceUnary, sealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _apartnessSeparationCompletion,
    _streamReadbackTolerance, _toleranceSealReplay, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed readbackUnary sealUnary route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback sealRow routeRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, route, provenancePkg, routePkg⟩
  }
  exact ⟨cert, routeUnary⟩

end BEDC.Derived.RealApartnessCompletionUp

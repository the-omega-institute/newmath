import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionObligationPartition [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay provenance
      localName separatedRead windowRead sealRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont apartness separation separatedRead →
        Cont stream readback windowRead →
          Cont windowRead sealRow sealRead →
            Cont transport replay structuralRead →
              PkgSig bundle sealRead pkg →
                PkgSig bundle structuralRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row sealRead ∨ hsame row structuralRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row apartness ∨ hsame row separation ∨
                          hsame row completion ∨ hsame row stream ∨ hsame row readback ∨
                            hsame row sealRow ∨ hsame row sealRead ∨
                              hsame row structuralRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                          Cont stream readback windowRead ∧
                              Cont windowRead sealRow sealRead ∧
                                Cont transport replay structuralRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle sealRead pkg ∧
                                      PkgSig bundle structuralRead pkg)
                      hsame ∧
                    UnaryHistory separatedRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute windowRoute sealRoute structuralRoute sealPkg structuralPkg
  obtain ⟨apartnessUnary, separationUnary, _completionUnary, streamUnary, readbackUnary,
    _toleranceUnary, sealUnary, transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary sealUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sealRead ∨ hsame row structuralRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row sealRead ∨ hsame row structuralRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont stream readback windowRead ∧ Cont windowRead sealRow sealRead ∧
                Cont transport replay structuralRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg ∧ PkgSig bundle structuralRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead
          ⟨Or.inl (hsame_refl sealRead), sealReadUnary⟩
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
        cases source.left with
        | inl sealSource =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sealSource),
                unary_transport source.right sameRows⟩
        | inr structuralSource =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) structuralSource),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sealSource =>
          right
          right
          right
          right
          right
          right
          left
          exact sealSource
      | inr structuralSource =>
          right
          right
          right
          right
          right
          right
          right
          exact structuralSource
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, separatedRoute, windowRoute, sealRoute, structuralRoute,
          provenancePkg, sealPkg, structuralPkg⟩
  }
  exact ⟨cert, separatedUnary, windowUnary, sealReadUnary, structuralReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp

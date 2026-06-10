import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionSeparatedCompletionHandoff [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay provenance
      localName separatedRead completionRead windowRead toleranceRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg ->
      Cont apartness separation separatedRead ->
        Cont separatedRead completion completionRead ->
          Cont stream readback windowRead ->
            Cont windowRead tolerance toleranceRead ->
              Cont toleranceRead sealRow sealedRead ->
                PkgSig bundle sealedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row apartness ∨ hsame row separation ∨
                          hsame row completion ∨ hsame row stream ∨ hsame row readback ∨
                            hsame row tolerance ∨ hsame row sealRow ∨
                              hsame row sealedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                          Cont separatedRead completion completionRead ∧
                            Cont stream readback windowRead ∧
                              Cont windowRead tolerance toleranceRead ∧
                                Cont toleranceRead sealRow sealedRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle sealedRead pkg)
                      hsame ∧
                    UnaryHistory separatedRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute completionRoute windowRoute toleranceRoute sealRoute sealedPkg
  obtain ⟨apartnessUnary, separationUnary, completionUnary, streamUnary, readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary completionUnary completionRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary toleranceUnary toleranceRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont separatedRead completion completionRead ∧
                Cont stream readback windowRead ∧ Cont windowRead tolerance toleranceRead ∧
                  Cont toleranceRead sealRow sealedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, separatedRoute, completionRoute, windowRoute, toleranceRoute,
          sealRoute, provenancePkg, sealedPkg⟩
  }
  exact
    ⟨cert, separatedUnary, completionReadUnary, windowReadUnary, toleranceReadUnary,
      sealedReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp

import BEDC.Derived.CauchyCompletionMinimalityUp.RouteInduction

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityDenseExtensionUniqueness [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead leftRead rightRead joinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      Cont completion embedding denseRead →
        Cont denseRead universal universalRead →
          Cont universalRead extension extensionRead →
            Cont extension separated leftRead →
              Cont extension separated rightRead →
                hsame leftRead rightRead →
                  Cont leftRead replay joinedRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle name pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row joinedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row denseRead ∨
                                hsame row universalRead ∨ hsame row extensionRead ∨
                                  hsame row leftRead ∨ hsame row rightRead ∨
                                    hsame row joinedRead ∨ hsame row separated ∨
                                      hsame row replay ∨ hsame row name)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont completion embedding denseRead ∧
                                Cont denseRead universal universalRead ∧
                                  Cont universalRead extension extensionRead ∧
                                    Cont extension separated leftRead ∧
                                      Cont extension separated rightRead ∧
                                        hsame leftRead rightRead ∧
                                          Cont leftRead replay joinedRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle name pkg)
                            hsame ∧
                          UnaryHistory denseRead ∧ UnaryHistory universalRead ∧
                            UnaryHistory extensionRead ∧ UnaryHistory leftRead ∧
                              UnaryHistory rightRead ∧ UnaryHistory joinedRead := by
  -- BEDC touchpoint anchor: CauchyCompletionMinimalityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute universalRoute extensionRoute leftRoute rightRoute sameSides
    joinedRoute provenancePkg namePkg
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, _carrierProvenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary universalUnary universalRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed universalReadUnary extensionUnary extensionRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed extensionUnary separatedUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed extensionUnary separatedUnary rightRoute
  have joinedUnary : UnaryHistory joinedRead :=
    unary_cont_closed leftUnary replayUnary joinedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row denseRead ∨ hsame row universalRead ∨
              hsame row extensionRead ∨ hsame row leftRead ∨ hsame row rightRead ∨
                hsame row joinedRead ∨ hsame row separated ∨ hsame row replay ∨
                  hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont denseRead universal universalRead ∧
                Cont universalRead extension extensionRead ∧
                  Cont extension separated leftRead ∧ Cont extension separated rightRead ∧
                    hsame leftRead rightRead ∧ Cont leftRead replay joinedRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joinedRead ⟨hsame_refl joinedRead, joinedUnary⟩
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
                    (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, universalRoute, extensionRoute, leftRoute, rightRoute,
          sameSides, joinedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, denseUnary, universalReadUnary, extensionReadUnary, leftUnary, rightUnary,
      joinedUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp

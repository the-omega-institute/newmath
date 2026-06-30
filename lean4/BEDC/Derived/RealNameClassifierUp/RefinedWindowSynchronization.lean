import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierRefinedWindowSynchronization [AskSetup] [PackageSetup]
    {sourceA sourceB commonWindow dyadicA dyadicB tolerance readbackA sealRow transport replay
      provenance localName refinedOne refinedTwo classifierOne classifierTwo sealOne sealTwo
      syncRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp sourceA commonWindow dyadicA dyadicB tolerance readbackA sealRow
        transport replay provenance localName bundle pkg →
      Cont commonWindow transport refinedOne →
        Cont refinedOne dyadicA classifierOne →
          Cont classifierOne dyadicB sealOne →
            Cont commonWindow transport refinedTwo →
              Cont refinedTwo dyadicA classifierTwo →
                Cont classifierTwo dyadicB sealTwo →
                  Cont sealOne sealTwo syncRead →
                    PkgSig bundle syncRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row syncRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row commonWindow ∨ hsame row transport ∨
                              hsame row refinedOne ∨ hsame row refinedTwo ∨
                                hsame row classifierOne ∨ hsame row classifierTwo ∨
                                  hsame row sealOne ∨ hsame row sealTwo ∨
                                    hsame row syncRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont sealOne sealTwo syncRead ∧
                              PkgSig bundle syncRead pkg)
                          hsame ∧
                        UnaryHistory refinedOne ∧ UnaryHistory refinedTwo ∧
                          UnaryHistory syncRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refineOneRoute classifierOneRoute sealOneRoute refineTwoRoute
    classifierTwoRoute sealTwoRoute syncRoute syncPkg
  have _sourceBReflexive : hsame sourceB sourceB := hsame_refl sourceB
  obtain ⟨_sourceUnary, commonWindowUnary, dyadicAUnary, dyadicBUnary, _toleranceUnary,
    _readbackAUnary, _sealRowUnary, transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceWindowReplay, _dyadicToleranceRoute, _toleranceReadbackSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have refinedOneUnary : UnaryHistory refinedOne :=
    unary_cont_closed commonWindowUnary transportUnary refineOneRoute
  have classifierOneUnary : UnaryHistory classifierOne :=
    unary_cont_closed refinedOneUnary dyadicAUnary classifierOneRoute
  have sealOneUnary : UnaryHistory sealOne :=
    unary_cont_closed classifierOneUnary dyadicBUnary sealOneRoute
  have refinedTwoUnary : UnaryHistory refinedTwo :=
    unary_cont_closed commonWindowUnary transportUnary refineTwoRoute
  have classifierTwoUnary : UnaryHistory classifierTwo :=
    unary_cont_closed refinedTwoUnary dyadicAUnary classifierTwoRoute
  have sealTwoUnary : UnaryHistory sealTwo :=
    unary_cont_closed classifierTwoUnary dyadicBUnary sealTwoRoute
  have syncUnary : UnaryHistory syncRead :=
    unary_cont_closed sealOneUnary sealTwoUnary syncRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row syncRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commonWindow ∨ hsame row transport ∨ hsame row refinedOne ∨
              hsame row refinedTwo ∨ hsame row classifierOne ∨ hsame row classifierTwo ∨
                hsame row sealOne ∨ hsame row sealTwo ∨ hsame row syncRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sealOne sealTwo syncRead ∧ PkgSig bundle syncRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro syncRead ⟨hsame_refl syncRead, syncUnary⟩
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
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, syncRoute, syncPkg⟩
  }
  exact ⟨cert, refinedOneUnary, refinedTwoUnary, syncUnary⟩

end BEDC.Derived.RealNameClassifierUp

import BEDC.Derived.EffectivePolishSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EffectivePolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EffectivePolishSpaceCarrier [AskSetup] [PackageSetup]
    (polish dense realizer stream readback tolerance realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory polish ∧ UnaryHistory dense ∧ UnaryHistory realizer ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont stream readback transport ∧
          Cont transport tolerance replay ∧ PkgSig bundle provenance pkg

theorem EffectivePolishSpaceRealizerHandoff
    {P D Q S R M L H C G N denseRead streamRead cauchyRead readbackRead sealRead
      namedRead : BHist} :
    UnaryHistory D ->
      UnaryHistory S ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory M ->
              UnaryHistory L ->
                UnaryHistory N ->
                  Cont D S denseRead ->
                    Cont denseRead Q cauchyRead ->
                      Cont cauchyRead R readbackRead ->
                        Cont readbackRead M sealRead ->
                          Cont sealRead N namedRead ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row P ∨ hsame row D ∨ hsame row Q ∨
                                    hsame row S ∨ hsame row R ∨ hsame row M ∨
                                      hsame row L ∨ hsame row H ∨ hsame row C ∨
                                        hsame row G ∨ hsame row N ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont D S denseRead ∧
                                    Cont denseRead Q cauchyRead ∧
                                      Cont cauchyRead R readbackRead ∧
                                        Cont readbackRead M sealRead ∧
                                          Cont sealRead N namedRead)
                                hsame ∧
                              UnaryHistory denseRead ∧ UnaryHistory cauchyRead ∧
                                UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: EffectivePolishSpaceUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro dUnary sUnary qUnary rUnary mUnary _lUnary nUnary denseRoute cauchyRoute
    readbackRoute sealRoute namedRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed dUnary sUnary denseRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed denseUnary qUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary mUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row D ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨
              hsame row M ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S denseRead ∧ Cont denseRead Q cauchyRead ∧
              Cont cauchyRead R readbackRead ∧ Cont readbackRead M sealRead ∧
                Cont sealRead N namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, cauchyRoute, readbackRoute, sealRoute, namedRoute⟩
  }
  exact ⟨cert, denseUnary, cauchyUnary, readbackUnary, sealUnary, namedUnary⟩

theorem EffectivePolishSpaceCompleteSeparableHandoff [AskSetup] [PackageSetup]
    {polish dense realizer stream readback tolerance realSeal transport replay provenance
      localName completeRead separableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EffectivePolishSpaceCarrier polish dense realizer stream readback tolerance realSeal
        transport replay provenance localName bundle pkg ->
      Cont dense realizer completeRead ->
        Cont completeRead realSeal separableRead ->
          PkgSig bundle separableRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row separableRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row polish ∨ hsame row dense ∨ hsame row realizer ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                      hsame row realSeal ∨ hsame row separableRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle separableRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory completeRead ∧ UnaryHistory separableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier completeRoute separableRoute separablePkg
  obtain
    ⟨_polishUnary, denseUnary, realizerUnary, _streamUnary, _readbackUnary,
      _toleranceUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, _streamReadbackRoute, _transportToleranceRoute, provenancePkg⟩ :=
    carrier
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed denseUnary realizerUnary completeRoute
  have separableUnary : UnaryHistory separableRead :=
    unary_cont_closed completeUnary realSealUnary separableRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row polish ∨ hsame row dense ∨ hsame row realizer ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row realSeal ∨ hsame row separableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle separableRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separableRead ⟨hsame_refl separableRead, separableUnary⟩
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
      exact ⟨source.right, separablePkg, provenancePkg⟩
  }
  exact ⟨cert, completeUnary, separableUnary⟩

theorem EffectivePolishSpaceCarrier_dense_realizer_transport [AskSetup] [PackageSetup]
    {polish dense realizer stream readback tolerance realSeal transport replay provenance
      localName denseRead cauchyRead readbackRead sealRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EffectivePolishSpaceCarrier polish dense realizer stream readback tolerance realSeal
        transport replay provenance localName bundle pkg ->
      Cont dense realizer denseRead ->
        Cont denseRead stream cauchyRead ->
          Cont cauchyRead readback readbackRead ->
            Cont readbackRead realSeal sealRead ->
              hsame sealRead transportedRead ->
                PkgSig bundle transportedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dense ∨ hsame row realizer ∨ hsame row stream ∨
                          hsame row readback ∨ hsame row realSeal ∨
                            hsame row transportedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle transportedRead pkg)
                      hsame ∧
                    UnaryHistory denseRead ∧ UnaryHistory cauchyRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier denseRoute cauchyRoute readbackRoute sealRoute sameSeal transportedPkg
  obtain
    ⟨_polishUnary, denseUnary, realizerUnary, streamUnary, readbackUnary, _toleranceUnary,
      realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      _streamReadbackRoute, _transportToleranceRoute, _provenancePkg⟩ :=
    carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary realizerUnary denseRoute
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed denseReadUnary streamUnary cauchyRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary realSealUnary sealRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport sealReadUnary sameSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dense ∨ hsame row realizer ∨ hsame row stream ∨ hsame row readback ∨
              hsame row realSeal ∨ hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle transportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
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
      exact ⟨source.right, transportedPkg⟩
  }
  exact ⟨cert, denseReadUnary, cauchyReadUnary, readbackReadUnary, transportedUnary⟩

end BEDC.Derived.EffectivePolishSpaceUp

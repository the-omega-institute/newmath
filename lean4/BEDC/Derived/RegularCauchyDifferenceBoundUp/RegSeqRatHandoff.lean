import BEDC.Derived.RegularCauchyDifferenceBoundUp

namespace BEDC.Derived.RegularCauchyDifferenceBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDifferenceBoundRegSeqRatHandoff [AskSetup] [PackageSetup]
    {X Y W D E R H C P N leftWindow rightWindow diffRead envelopeRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDifferenceBoundCarrier X Y W D E R H C P N bundle pkg →
      Cont X W leftWindow →
        Cont Y W rightWindow →
          Cont W D diffRead →
            Cont diffRead E envelopeRead →
              Cont envelopeRead R sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row Y ∨ hsame row W ∨ hsame row D ∨
                          hsame row E ∨ hsame row R ∨ hsame row leftWindow ∨
                            hsame row rightWindow ∨ hsame row diffRead ∨
                              hsame row envelopeRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont X W leftWindow ∧
                          Cont Y W rightWindow ∧ Cont W D diffRead ∧
                            Cont diffRead E envelopeRead ∧ Cont envelopeRead R sealRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                      UnaryHistory diffRead ∧ UnaryHistory envelopeRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyDifferenceBoundCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftWindowRoute rightWindowRoute diffRoute envelopeRoute sealRoute sealPkg
  obtain ⟨xUnary, yUnary, wUnary, dUnary, eUnary, rUnary, _hUnary, _cUnary, pUnary,
    _nUnary, _sourceWindow, _dyadicEnvelope, _sealTransport, _localReplay,
    provenancePkg⟩ := carrier
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed xUnary wUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed yUnary wUnary rightWindowRoute
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed wUnary dUnary diffRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed diffUnary eUnary envelopeRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed envelopeUnary rUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row W ∨ hsame row D ∨ hsame row E ∨
              hsame row R ∨ hsame row leftWindow ∨ hsame row rightWindow ∨
                hsame row diffRead ∨ hsame row envelopeRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W leftWindow ∧ Cont Y W rightWindow ∧
              Cont W D diffRead ∧ Cont diffRead E envelopeRead ∧
                Cont envelopeRead R sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftWindowRoute, rightWindowRoute, diffRoute, envelopeRoute,
          sealRoute, provenancePkg, sealPkg⟩
  }
  exact
    ⟨cert, leftWindowUnary, rightWindowUnary, diffUnary, envelopeUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyDifferenceBoundUp

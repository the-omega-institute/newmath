import BEDC.Derived.RegularCauchyFilterUp

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_basis_rows [AskSetup] [PackageSetup]
    {B R T D M E H C P N basisRead regReadback realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory T ->
        UnaryHistory D ->
          UnaryHistory M ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont B T (append B T) ->
                  Cont T D (append T D) ->
                    Cont (append T D) M basisRead ->
                      Cont basisRead R regReadback ->
                        Cont regReadback E realSealRead ->
                          PkgSig bundle realSealRead pkg ->
                            regularCauchyFilterFromEventFlow
                                (regularCauchyFilterToEventFlow
                                  (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
                              some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
                                    hsame row R ∨ hsame row E ∨
                                      Cont regReadback E realSealRead)
                                (fun row : BHist =>
                                  PkgSig bundle realSealRead pkg ∧ hsame row realSealRead)
                                hsame ∧
                              UnaryHistory basisRead ∧ UnaryHistory regReadback ∧
                                UnaryHistory realSealRead ∧ Cont (append T D) M basisRead ∧
                                  Cont basisRead R regReadback ∧
                                    Cont regReadback E realSealRead ∧
                                      PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _bUnary tUnary dUnary mUnary rUnary eUnary _btRoute _tdRoute basisRoute
    regRoute sealRoute sealPkg
  have hdecode :
      ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have roundTrip :
      regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow
            (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) := by
    rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
      hdecode B, hdecode R, hdecode T, hdecode D, hdecode M, hdecode E,
      hdecode H, hdecode C, hdecode P, hdecode N]
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed (unary_cont_closed tUnary dUnary rfl) mUnary basisRoute
  have readbackUnary : UnaryHistory regReadback :=
    unary_cont_closed basisUnary rUnary regRoute
  have sealUnary : UnaryHistory realSealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have sourceReal : hsame realSealRead realSealRead ∧ UnaryHistory realSealRead :=
    ⟨hsame_refl realSealRead, sealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
            hsame row R ∨ hsame row E ∨ Cont regReadback E realSealRead)
        (fun row : BHist => PkgSig bundle realSealRead pkg ∧ hsame row realSealRead)
        hsame := by
    refine
      { core :=
          { carrier_inhabited := ?carrier_inhabited
            equiv_refl := ?equiv_refl
            equiv_symm := ?equiv_symm
            equiv_trans := ?equiv_trans
            carrier_respects_equiv := ?carrier_respects_equiv }
        pattern_sound := ?pattern_sound
        ledger_sound := ?ledger_sound }
    · exact Exists.intro realSealRead sourceReal
    · intro row _source
      exact hsame_refl row
    · intro _row _target same
      exact hsame_symm same
    · intro _row _target _next sameRowTarget sameTargetNext
      exact hsame_trans sameRowTarget sameTargetNext
    · intro _row _target same source
      cases same
      exact source
    · intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRoute)))))
    · intro _row source
      exact ⟨sealPkg, source.left⟩
  exact
    ⟨roundTrip, cert, basisUnary, readbackUnary, sealUnary, basisRoute, regRoute,
      sealRoute, sealPkg⟩

end BEDC.Derived.RegularCauchyFilterUp

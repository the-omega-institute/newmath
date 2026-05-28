import BEDC.Derived.RegularCauchyFilterUp

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_mature_route_exhaustion
    [AskSetup] [PackageSetup]
    {B R T D M E H C P N windowRead basisRead regReadback realSealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory P ->
                Cont T D windowRead ->
                  Cont windowRead M basisRead ->
                    Cont basisRead R regReadback ->
                      Cont regReadback E realSealRead ->
                        Cont realSealRead P publicRead ->
                          PkgSig bundle publicRead pkg ->
                            regularCauchyFilterFromEventFlow
                                (regularCauchyFilterToEventFlow
                                  (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
                              some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
                                    hsame row R ∨ hsame row E ∨ hsame row P ∨
                                      Cont realSealRead P publicRead)
                                (fun row : BHist =>
                                  PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                                hsame ∧
                              UnaryHistory windowRead ∧ UnaryHistory basisRead ∧
                                UnaryHistory regReadback ∧ UnaryHistory realSealRead ∧
                                  UnaryHistory publicRead ∧ Cont T D windowRead ∧
                                    Cont windowRead M basisRead ∧
                                      Cont basisRead R regReadback ∧
                                        Cont regReadback E realSealRead ∧
                                          Cont realSealRead P publicRead ∧
                                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro tUnary dUnary mUnary rUnary eUnary pUnary windowRoute basisRoute regRoute
    sealRoute publicRoute publicPkg
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
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tUnary dUnary windowRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowUnary mUnary basisRoute
  have readbackUnary : UnaryHistory regReadback :=
    unary_cont_closed basisUnary rUnary regRoute
  have sealUnary : UnaryHistory realSealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary pUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨ hsame row R ∨
            hsame row E ∨ hsame row P ∨ Cont realSealRead P publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other publicRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr publicRoute))))))
    ledger_sound := by
      intro _row source
      exact ⟨publicPkg, source.left⟩
  }
  exact
    ⟨roundTrip, cert, windowUnary, basisUnary, readbackUnary, sealUnary, publicUnary,
      windowRoute, basisRoute, regRoute, sealRoute, publicRoute, publicPkg⟩

end BEDC.Derived.RegularCauchyFilterUp

import BEDC.Derived.RegularCauchyFilterUp

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_scoped_handoff
    [AskSetup] [PackageSetup]
    {B R T D M E H C P N windowRead basisRead regReadback realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont T D windowRead ->
                Cont windowRead M basisRead ->
                  Cont basisRead R regReadback ->
                    Cont regReadback E realSealRead ->
                      PkgSig bundle realSealRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨
                                hsame row R ∨ hsame row E ∨ Cont regReadback E realSealRead)
                            (fun row : BHist =>
                              PkgSig bundle realSealRead pkg ∧ hsame row realSealRead)
                            hsame ∧
                          UnaryHistory windowRead ∧ UnaryHistory basisRead ∧
                            UnaryHistory regReadback ∧ UnaryHistory realSealRead ∧
                              Cont T D windowRead ∧ Cont windowRead M basisRead ∧
                                Cont basisRead R regReadback ∧
                                  Cont regReadback E realSealRead ∧
                                    PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro tUnary dUnary mUnary rUnary eUnary windowRoute basisRoute regRoute sealRoute
    sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tUnary dUnary windowRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowUnary mUnary basisRoute
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
          hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨ hsame row R ∨
            hsame row E ∨ Cont regReadback E realSealRead)
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
    · intro row target same
      exact hsame_symm same
    · intro row target next sameRowTarget sameTargetNext
      exact hsame_trans sameRowTarget sameTargetNext
    · intro row target same source
      cases same
      exact source
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRoute)))))
    · intro row source
      exact ⟨sealPkg, source.left⟩
  exact
    ⟨cert, windowUnary, basisUnary, readbackUnary, sealUnary, windowRoute,
      basisRoute, regRoute, sealRoute, sealPkg⟩

theorem RegularCauchyFilterCarrier_directed_refinement_normal_form
    [AskSetup] [PackageSetup]
    {B R T D M E H C P N windowRead basisRead regRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont T D windowRead ->
                Cont windowRead M basisRead ->
                  Cont basisRead R regRead ->
                    Cont regRead E realRead ->
                      PkgSig bundle realRead pkg ->
                        regularCauchyFilterFromEventFlow
                            (regularCauchyFilterToEventFlow
                              (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
                          some (RegularCauchyFilterUp.mk B R T D M E H C P N) ∧
                          SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row D ∨ hsame row M ∨
                                  hsame row R ∨ hsame row E ∨ Cont regRead E realRead)
                              (fun row : BHist =>
                                PkgSig bundle realRead pkg ∧ hsame row realRead)
                              hsame ∧
                            UnaryHistory windowRead ∧ UnaryHistory basisRead ∧
                              UnaryHistory regRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro tUnary dUnary mUnary rUnary eUnary windowRoute basisRoute regRoute realRoute
    realPkg
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
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed basisUnary rUnary regRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row D ∨ hsame row M ∨ hsame row R ∨
              hsame row E ∨ Cont regRead E realRead)
          (fun row : BHist => PkgSig bundle realRead pkg ∧ hsame row realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        have otherSame : hsame other realRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨realPkg, source.left⟩
  }
  exact ⟨roundTrip, cert, windowUnary, basisUnary, regUnary, realUnary⟩

theorem RegularCauchyFilterCarrier_scoped_public_package
    [AskSetup] [PackageSetup]
    {B R T D M E H C P N basisRead regRead realRead : BHist}
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
                      Cont basisRead R regRead ->
                        Cont regRead E realRead ->
                          PkgSig bundle realRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row T ∨ hsame row D ∨
                                    hsame row M ∨ hsame row R ∨ hsame row E ∨
                                      Cont regRead E realRead)
                                (fun row : BHist =>
                                  PkgSig bundle realRead pkg ∧ hsame row realRead)
                                hsame ∧
                              UnaryHistory (append B T) ∧
                                UnaryHistory (append T D) ∧
                                  UnaryHistory basisRead ∧ UnaryHistory regRead ∧
                                    UnaryHistory realRead ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro bUnary tUnary dUnary mUnary rUnary eUnary baseRoute tailRoute basisRoute
    regRoute realRoute realPkg
  have baseTailUnary : UnaryHistory (append B T) :=
    unary_cont_closed bUnary tUnary baseRoute
  have tailDyadicUnary : UnaryHistory (append T D) :=
    unary_cont_closed tUnary dUnary tailRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed tailDyadicUnary mUnary basisRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed basisUnary rUnary regRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row T ∨ hsame row D ∨ hsame row M ∨ hsame row R ∨
              hsame row E ∨ Cont regRead E realRead)
          (fun row : BHist => PkgSig bundle realRead pkg ∧ hsame row realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        have otherSame : hsame other realRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨realPkg, source.left⟩
  }
  exact
    ⟨cert, baseTailUnary, tailDyadicUnary, basisUnary, regUnary, realUnary, realPkg⟩

end BEDC.Derived.RegularCauchyFilterUp

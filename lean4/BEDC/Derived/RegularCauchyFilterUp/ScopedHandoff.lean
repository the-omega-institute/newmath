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

end BEDC.Derived.RegularCauchyFilterUp

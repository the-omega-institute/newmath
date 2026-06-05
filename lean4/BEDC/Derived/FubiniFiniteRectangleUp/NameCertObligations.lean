import BEDC.FKernel.Ask
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FubiniFiniteRectangleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem FubiniFiniteRectangleNamecertObligations [AskSetup] [PackageSetup]
    {R M I P A B D S E H C Q N _rectangleRead measureRead integralRead productRead
      firstRoute secondRoute toleranceRead rationalRead sealRead replayRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R -> UnaryHistory M -> UnaryHistory I -> UnaryHistory P ->
      UnaryHistory A -> UnaryHistory B -> UnaryHistory D -> UnaryHistory S ->
        UnaryHistory E -> UnaryHistory H -> UnaryHistory C -> UnaryHistory Q ->
          UnaryHistory N -> Cont R M measureRead -> Cont measureRead I integralRead ->
            Cont integralRead P productRead -> Cont productRead A firstRoute ->
              Cont productRead B secondRoute -> Cont firstRoute D toleranceRead ->
                Cont secondRoute D rationalRead -> Cont rationalRead E sealRead ->
                  Cont H C replayRead -> Cont Q N nameRead -> PkgSig bundle Q pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row R ∨ hsame row M ∨ hsame row I ∨ hsame row P ∨
                              hsame row A ∨ hsame row B ∨ hsame row D ∨ hsame row S ∨
                                hsame row E ∨ hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory measureRead ∧ UnaryHistory integralRead ∧
                          UnaryHistory productRead ∧ UnaryHistory firstRoute ∧
                            UnaryHistory secondRoute ∧ UnaryHistory toleranceRead ∧
                              UnaryHistory rationalRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro rectangleUnary measureUnary integralUnary productUnary firstUnary secondUnary
    toleranceUnary rationalUnary realUnary hUnary cUnary qUnary nUnary measureRoute
    integralRoute productRoute firstRouteCont secondRouteCont toleranceRoute rationalRoute
    sealRoute replayRoute nameRoute provenancePkg namePkg
  have measureReadUnary : UnaryHistory measureRead :=
    unary_cont_closed rectangleUnary measureUnary measureRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed measureReadUnary integralUnary integralRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed integralReadUnary productUnary productRoute
  have firstRouteUnary : UnaryHistory firstRoute :=
    unary_cont_closed productReadUnary firstUnary firstRouteCont
  have secondRouteUnary : UnaryHistory secondRoute :=
    unary_cont_closed productReadUnary secondUnary secondRouteCont
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed firstRouteUnary toleranceUnary toleranceRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed secondRouteUnary toleranceUnary rationalRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalReadUnary realUnary sealRoute
  have _replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have _nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed qUnary nUnary nameRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  · exact
      ⟨measureReadUnary, integralReadUnary, productReadUnary, firstRouteUnary,
        secondRouteUnary, toleranceReadUnary, rationalReadUnary, sealReadUnary⟩

end BEDC.Derived.FubiniFiniteRectangleUp

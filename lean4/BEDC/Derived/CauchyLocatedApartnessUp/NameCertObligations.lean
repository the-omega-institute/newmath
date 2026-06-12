import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLocatedApartnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLocatedApartnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q A B S R D E H C P N locatorRead apartnessRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory B ->
                UnaryHistory E ->
                  Cont Q S locatorRead ->
                    Cont locatorRead D apartnessRead ->
                      Cont apartnessRead E sealRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row A ∨ hsame row B ∨
                                  hsame row S ∨ hsame row R ∨ hsame row D ∨
                                    hsame row E ∨ hsame row H ∨ hsame row C ∨
                                      hsame row P ∨ hsame row N ∨ hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q S locatorRead ∧
                                  Cont locatorRead D apartnessRead ∧
                                    Cont apartnessRead E sealRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                              UnaryHistory locatorRead ∧ UnaryHistory apartnessRead ∧
                                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro qUnary sUnary _rUnary dUnary _aUnary _bUnary eUnary locatorRoute
    apartnessRoute sealRoute provenancePkg namePkg
  have locatorUnary : UnaryHistory locatorRead :=
    unary_cont_closed qUnary sUnary locatorRoute
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed locatorUnary dUnary apartnessRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed apartnessUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row A ∨ hsame row B ∨ hsame row S ∨
            hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Q S locatorRead ∧
            Cont locatorRead D apartnessRead ∧ Cont apartnessRead E sealRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      have routeSeal : hsame _row N ∨ hsame _row sealRead :=
        Or.inr source.left
      have routeName :
          hsame _row P ∨ hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeSeal
      have routePkg :
          hsame _row C ∨ hsame _row P ∨ hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeName
      have routeReplay :
          hsame _row H ∨ hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
            hsame _row sealRead :=
        Or.inr routePkg
      have routeSealRow :
          hsame _row E ∨ hsame _row H ∨ hsame _row C ∨ hsame _row P ∨
            hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeReplay
      have routeTolerance :
          hsame _row D ∨ hsame _row E ∨ hsame _row H ∨ hsame _row C ∨
            hsame _row P ∨ hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeSealRow
      have routeReadback :
          hsame _row R ∨ hsame _row D ∨ hsame _row E ∨ hsame _row H ∨
            hsame _row C ∨ hsame _row P ∨ hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeTolerance
      have routeWindow :
          hsame _row S ∨ hsame _row R ∨ hsame _row D ∨ hsame _row E ∨
            hsame _row H ∨ hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
              hsame _row sealRead :=
        Or.inr routeReadback
      have routeEndpointB :
          hsame _row B ∨ hsame _row S ∨ hsame _row R ∨ hsame _row D ∨
            hsame _row E ∨ hsame _row H ∨ hsame _row C ∨ hsame _row P ∨
              hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeWindow
      have routeEndpointA :
          hsame _row A ∨ hsame _row B ∨ hsame _row S ∨ hsame _row R ∨
            hsame _row D ∨ hsame _row E ∨ hsame _row H ∨ hsame _row C ∨
              hsame _row P ∨ hsame _row N ∨ hsame _row sealRead :=
        Or.inr routeEndpointB
      exact Or.inr routeEndpointA
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, locatorRoute, apartnessRoute, sealRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, locatorUnary, apartnessUnary, sealUnary⟩

end BEDC.Derived.CauchyLocatedApartnessUp

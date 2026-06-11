import BEDC.Derived.LocatedCauchyFilterUp.ChoiceFreeBasis

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterRegularSequenceHandoff [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N basisRead dyadicRead regularRead streamRead readbackRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterCarrier F B R S Q D T E H C P N bundle pkg →
      Cont F B basisRead →
        Cont basisRead D dyadicRead →
          Cont dyadicRead R regularRead →
            Cont regularRead S streamRead →
              Cont streamRead Q readbackRead →
                Cont readbackRead E realRead →
                  PkgSig bundle realRead pkg →
                    UnaryHistory streamRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory realRead ∧
                        Cont regularRead S streamRead ∧ Cont streamRead Q readbackRead ∧
                          Cont readbackRead E realRead ∧ hsame E E ∧
                            PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier basisCont dyadicCont regularCont streamCont readbackCont realCont realPkg
  obtain ⟨unaryF, unaryB, unaryR, unaryS, unaryQ, unaryD, unaryT, unaryE,
    _unaryH, _unaryC, unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have route :=
    LocatedCauchyFilterBasisRefinementRoute
      (F := F) (B := B) (R := R) (S := S) (Q := Q) (D := D) (T := T) (E := E)
      (H := H) (C := C) (P := P) (N := N) (basisRead := basisRead) (dyadicRead := dyadicRead)
      (regularRead := regularRead) (streamRead := streamRead)
      (readbackRead := readbackRead) (realRead := realRead) (bundle := bundle)
      (pkg := pkg) unaryF unaryB unaryR unaryS unaryQ unaryD unaryT unaryE unaryP
      basisCont dyadicCont regularCont streamCont readbackCont realCont provenancePkg realPkg
  obtain ⟨_basisUnary, dyadicUnary, _regularUnary, streamUnary, readbackUnary,
    realUnary, _basisCont, _dyadicCont, _regularCont, _streamCont, _readbackCont,
      _realCont, _routeProvenancePkg, routeRealPkg⟩ := route
  exact
    ⟨streamUnary, readbackUnary, dyadicUnary, realUnary, streamCont, readbackCont,
      realCont, hsame_refl E, routeRealPkg⟩

end BEDC.Derived.LocatedCauchyFilterUp

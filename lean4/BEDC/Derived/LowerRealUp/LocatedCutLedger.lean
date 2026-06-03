import BEDC.Derived.LowerRealUp.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerRealLocatedCutLedger [AskSetup] [PackageSetup]
    {L0 W R E H C P N locatedRead rationalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont L0 W locatedRead ->
                Cont locatedRead R rationalRead ->
                  Cont rationalRead E realRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        UnaryHistory locatedRead ∧
                          UnaryHistory rationalRead ∧
                            UnaryHistory realRead ∧
                              hsame (lowerRealDecodeBHist (lowerRealEncodeBHist L0)) L0 ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig hsame
  intro fieldRows l0Unary windowUnary rationalUnary realUnary locatedRoute rationalRoute
    realRoute provenancePkg namePkg
  cases fieldRows
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed l0Unary windowUnary locatedRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed locatedUnary rationalUnary rationalRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary realUnary realRoute
  have lowerDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist L0)) L0 := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist L0) = L0
    exact LowerRealTasteGate_single_carrier_alignment.1 L0
  exact
    ⟨locatedUnary, rationalReadUnary, realReadUnary, lowerDecode, provenancePkg, namePkg⟩

end BEDC.Derived.LowerRealUp

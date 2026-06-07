import BEDC.Derived.DyadicUp.TasteGate

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicExponentShiftComposition [AskSetup] [PackageSetup]
    {Q0 S0 R0 E0 H0 C0 P0 N0 Q1 S1 R1 E1 H1 C1 P1 N1 commonQ commonS commonR
      commonE : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    DyadicCarrier Q0 S0 R0 E0 H0 C0 P0 N0 bundle0 pkg0 ->
      DyadicCarrier Q1 S1 R1 E1 H1 C1 P1 N1 bundle1 pkg1 ->
        Cont Q0 Q1 commonQ ->
          Cont S0 S1 commonS ->
            Cont commonQ commonS commonR ->
              Cont E0 E1 commonE ->
                UnaryHistory commonQ ∧ UnaryHistory commonS ∧ UnaryHistory commonR ∧
                  UnaryHistory commonE ∧ Cont commonQ commonS commonR ∧
                    Cont E0 E1 commonE := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier0 carrier1 qCommon sCommon qsCommon eCommon
  obtain ⟨q0Unary, s0Unary, _r0Unary, e0Unary, _h0Unary, _c0Unary, _p0Unary,
    _n0Unary, _qsr0Route, _rec0Route, _provenance0Pkg, _name0Pkg⟩ := carrier0
  obtain ⟨q1Unary, s1Unary, _r1Unary, e1Unary, _h1Unary, _c1Unary, _p1Unary,
    _n1Unary, _qsr1Route, _rec1Route, _provenance1Pkg, _name1Pkg⟩ := carrier1
  have commonQUnary : UnaryHistory commonQ :=
    unary_cont_closed q0Unary q1Unary qCommon
  have commonSUnary : UnaryHistory commonS :=
    unary_cont_closed s0Unary s1Unary sCommon
  have commonRUnary : UnaryHistory commonR :=
    unary_cont_closed commonQUnary commonSUnary qsCommon
  have commonEUnary : UnaryHistory commonE :=
    unary_cont_closed e0Unary e1Unary eCommon
  exact
    ⟨commonQUnary, commonSUnary, commonRUnary, commonEUnary, qsCommon, eCommon⟩

end BEDC.Derived.DyadicUp

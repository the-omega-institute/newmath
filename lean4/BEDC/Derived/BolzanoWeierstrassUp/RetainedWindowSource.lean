import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_retained_window_source [AskSetup] [PackageSetup]
    {S K R Q E H C P N boundedSource intervalNet regularSubsequence streamWindow
      ratReadback toleranceRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S H boundedSource ->
        Cont boundedSource K intervalNet ->
          Cont intervalNet R regularSubsequence ->
            Cont regularSubsequence C streamWindow ->
              Cont streamWindow Q ratReadback ->
                Cont ratReadback N toleranceRead ->
                  Cont toleranceRead E realSeal ->
                    PkgSig bundle realSeal pkg ->
                      UnaryHistory boundedSource ∧ UnaryHistory intervalNet ∧
                        UnaryHistory regularSubsequence ∧ UnaryHistory streamWindow ∧
                          UnaryHistory ratReadback ∧ UnaryHistory toleranceRead ∧
                            UnaryHistory realSeal ∧ Cont S H boundedSource ∧
                              Cont boundedSource K intervalNet ∧
                                Cont intervalNet R regularSubsequence ∧
                                  Cont regularSubsequence C streamWindow ∧
                                    Cont streamWindow Q ratReadback ∧
                                      Cont ratReadback N toleranceRead ∧
                                        Cont toleranceRead E realSeal ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier boundedRoute intervalRoute regularRoute windowRoute readbackRoute
    toleranceRoute sealRoute sealPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, CUnary, _PUnary,
    NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedSource :=
    unary_cont_closed SUnary HUnary boundedRoute
  have intervalUnary : UnaryHistory intervalNet :=
    unary_cont_closed boundedUnary KUnary intervalRoute
  have regularUnary : UnaryHistory regularSubsequence :=
    unary_cont_closed intervalUnary RUnary regularRoute
  have windowUnary : UnaryHistory streamWindow :=
    unary_cont_closed regularUnary CUnary windowRoute
  have readbackUnary : UnaryHistory ratReadback :=
    unary_cont_closed windowUnary QUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary NUnary toleranceRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed toleranceUnary EUnary sealRoute
  exact
    ⟨boundedUnary, intervalUnary, regularUnary, windowUnary, readbackUnary,
      toleranceUnary, sealUnary, boundedRoute, intervalRoute, regularRoute, windowRoute,
      readbackRoute, toleranceRoute, sealRoute, carrierPkg, sealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp

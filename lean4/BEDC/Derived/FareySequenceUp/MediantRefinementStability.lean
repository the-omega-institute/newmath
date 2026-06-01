import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceMediantRefinementStability [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacent mediant stern budget approx realSeal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory A ->
        UnaryHistory M ->
          UnaryHistory L ->
            UnaryHistory T ->
              UnaryHistory S ->
                UnaryHistory W ->
                  UnaryHistory R ->
                    UnaryHistory G ->
                      UnaryHistory E ->
                        Cont B A adjacent ->
                          Cont adjacent M mediant ->
                            Cont mediant S stern ->
                              Cont stern L budget ->
                                Cont budget T approx ->
                                  Cont approx G realSeal ->
                                    PkgSig bundle N pkg ->
                                      UnaryHistory adjacent ∧ UnaryHistory mediant ∧
                                        UnaryHistory stern ∧ UnaryHistory budget ∧
                                          UnaryHistory approx ∧ UnaryHistory realSeal ∧
                                            PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro boundaryUnary adjacencyUnary mediantCarrierUnary levelUnary toleranceUnary
    sternCarrierUnary _windowUnary _regularUnary approximationUnary _sealUnary
    adjacentRoute mediantRoute sternRoute budgetRoute approxRoute realSealRoute namePkg
  have _supportRows : BHist × BHist × BHist × BHist × BHist := (D, Q, H, C, P)
  have adjacentUnary : UnaryHistory adjacent :=
    unary_cont_closed boundaryUnary adjacencyUnary adjacentRoute
  have mediantUnary : UnaryHistory mediant :=
    unary_cont_closed adjacentUnary mediantCarrierUnary mediantRoute
  have sternUnary : UnaryHistory stern :=
    unary_cont_closed mediantUnary sternCarrierUnary sternRoute
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed sternUnary levelUnary budgetRoute
  have approxUnary : UnaryHistory approx :=
    unary_cont_closed budgetUnary toleranceUnary approxRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed approxUnary approximationUnary realSealRoute
  exact
    ⟨adjacentUnary, mediantUnary, sternUnary, budgetUnary, approxUnary, realSealUnary,
      namePkg⟩

end BEDC.Derived.FareySequenceUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRegSeqRatCarrier [AskSetup] [PackageSetup]
    (D S R Q W H K P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Q ∧
    UnaryHistory W ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory N ∧
      Cont D S R ∧ Cont R Q W ∧ Cont W H K ∧ PkgSig bundle P pkg

theorem LocatedRegSeqRatCarrier_tail_window_stability [AskSetup] [PackageSetup]
    {D S R Q W H K P N request locatedRead replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRegSeqRatCarrier D S R Q W H K P N bundle pkg →
      Cont D S request →
        Cont request Q locatedRead →
          Cont locatedRead H replay →
            PkgSig bundle replay pkg →
              UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory request ∧
                UnaryHistory locatedRead ∧ UnaryHistory replay ∧ Cont D S request ∧
                  Cont request Q locatedRead ∧ Cont locatedRead H replay ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier requestRoute locatedRoute replayRoute replayPkg
  obtain ⟨dUnary, sUnary, _rUnary, qUnary, _wUnary, hUnary, _kUnary, _nUnary,
    _dsr, _rqw, _whk, pPkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed dUnary sUnary requestRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed requestUnary qUnary locatedRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed locatedUnary hUnary replayRoute
  exact
    ⟨dUnary, sUnary, qUnary, requestUnary, locatedUnary, replayUnary, requestRoute,
      locatedRoute, replayRoute, pPkg, replayPkg⟩

end BEDC.Derived.LocatedRegSeqRatUp

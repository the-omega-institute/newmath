import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRealApartnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive CauchyRealApartnessUp : Type where
  | mk (E0 E1 R0 R1 W0 W1 D T H C P N : BHist) : CauchyRealApartnessUp
  deriving DecidableEq

def CauchyRealApartnessCarrier [AskSetup] [PackageSetup]
    (e0 e1 r0 r1 w0 w1 d t h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory e0 ∧ UnaryHistory e1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
    UnaryHistory w0 ∧ UnaryHistory w1 ∧ UnaryHistory d ∧ UnaryHistory t ∧
      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
        Cont t h c ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg

theorem CauchyRealApartnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {e0 e1 r0 r1 w0 w1 d t h c p n regularRead gapRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealApartnessCarrier e0 e1 r0 r1 w0 w1 d t h c p n bundle pkg →
      Cont w0 r0 regularRead →
        Cont regularRead d gapRead →
          Cont gapRead e0 realRead →
            PkgSig bundle n pkg →
              UnaryHistory regularRead ∧ UnaryHistory gapRead ∧ UnaryHistory realRead ∧
                Cont w0 r0 regularRead ∧ Cont regularRead d gapRead ∧
                  Cont gapRead e0 realRead ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRegularRead regularGapRead gapRealRead namePkg
  obtain ⟨e0Unary, _e1Unary, r0Unary, _r1Unary, w0Unary, _w1Unary, dUnary, _tUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _transportCont, provenancePkg, _carrierNamePkg⟩ :=
    carrier
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed w0Unary r0Unary windowRegularRead
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed regularReadUnary dUnary regularGapRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed gapReadUnary e0Unary gapRealRead
  exact
    ⟨regularReadUnary,
      gapReadUnary,
      realReadUnary,
      windowRegularRead,
      regularGapRead,
      gapRealRead,
      provenancePkg,
      namePkg⟩

end BEDC.Derived.CauchyRealApartnessUp

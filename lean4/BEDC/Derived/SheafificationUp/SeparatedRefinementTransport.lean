import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCarrier_separated_refinement_transport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N separatedRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L separatedRead →
        hsame separatedRead transportedRead →
          UnaryHistory separatedRead ∧ UnaryHistory transportedRead ∧
            Cont P L separatedRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier separatedRoute sameTransport
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, namePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed pUnary lUnary separatedRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport separatedUnary sameTransport
  exact ⟨separatedUnary, transportedUnary, separatedRoute, namePkg⟩

end BEDC.Derived.SheafificationUp

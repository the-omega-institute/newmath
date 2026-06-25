import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationGluingLedgerScope [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localFamily gluedRead sheafRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localFamily →
        Cont localFamily G gluedRead →
          Cont gluedRead S sheafRead →
            Cont sheafRead R replayRead →
              PkgSig bundle replayRead pkg →
                UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory S ∧
                  UnaryHistory localFamily ∧ UnaryHistory gluedRead ∧
                    UnaryHistory sheafRead ∧ UnaryHistory replayRead ∧
                      Cont P L localFamily ∧ Cont localFamily G gluedRead ∧
                        Cont gluedRead S sheafRead ∧ Cont sheafRead R replayRead ∧
                          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                            PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier localRoute glueRoute sheafRoute replayRoute replayPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    rUnary, _qUnary, _nUnary, qPkg, namePkg⟩ := carrier
  have localFamilyUnary : UnaryHistory localFamily :=
    unary_cont_closed pUnary lUnary localRoute
  have gluedReadUnary : UnaryHistory gluedRead :=
    unary_cont_closed localFamilyUnary gUnary glueRoute
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluedReadUnary sUnary sheafRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed sheafReadUnary rUnary replayRoute
  exact
    ⟨lUnary, gUnary, sUnary, localFamilyUnary, gluedReadUnary, sheafReadUnary,
      replayReadUnary, localRoute, glueRoute, sheafRoute, replayRoute, qPkg, namePkg,
      replayPkg⟩

end BEDC.Derived.SheafificationUp

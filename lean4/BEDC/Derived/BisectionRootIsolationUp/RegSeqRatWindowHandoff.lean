import BEDC.Derived.BisectionRootIsolationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BisectionRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BisectionRootIsolationCarrier [AskSetup] [PackageSetup]
    (interval bisection functionRow endpoint window readback sealRow transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory interval ∧ UnaryHistory bisection ∧ UnaryHistory functionRow ∧
    UnaryHistory endpoint ∧ UnaryHistory window ∧ UnaryHistory readback ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont window readback sealRow ∧
          Cont interval bisection endpoint ∧ PkgSig bundle provenance pkg

theorem BisectionRootIsolationRegSeqRatWindowHandoff [AskSetup] [PackageSetup]
    {interval bisection functionRow endpoint window readback sealRow transport replay provenance name
      observed exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BisectionRootIsolationCarrier interval bisection functionRow endpoint window readback sealRow
        transport replay provenance name bundle pkg →
      Cont window readback observed →
        Cont observed sealRow exported →
          PkgSig bundle exported pkg →
            UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory observed ∧
              UnaryHistory exported ∧ Cont window readback observed ∧
                Cont observed sealRow exported ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier observedRoute exportedRoute exportedPkg
  obtain ⟨_intervalUnary, _bisectionUnary, _functionUnary, _endpointUnary, windowUnary,
    readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _sealRoute, _endpointRoute, provenancePkg⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed windowUnary readbackUnary observedRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed observedUnary sealUnary exportedRoute
  exact
    ⟨windowUnary, readbackUnary, observedUnary, exportedUnary, observedRoute,
      exportedRoute, provenancePkg, exportedPkg⟩

end BEDC.Derived.BisectionRootIsolationUp

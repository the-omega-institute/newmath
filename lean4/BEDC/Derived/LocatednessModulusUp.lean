import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatednessModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatednessModulusCarrier [AskSetup] [PackageSetup]
    (request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory request ∧ UnaryHistory locatedInterval ∧ UnaryHistory rationalCells ∧
    UnaryHistory dyadicRows ∧ UnaryHistory streamWindow ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LocatednessModulusCarrier_window_transport [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead streamWindow windowRead →
          Cont windowRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory request ∧ UnaryHistory locatedInterval ∧ UnaryHistory cellRead ∧
                UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                  Cont request locatedInterval cellRead ∧
                    Cont cellRead streamWindow windowRead ∧
                      Cont windowRead realSeal sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier requestLocated cellWindow windowSeal sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, _dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cellUnary streamUnary cellWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary realSealUnary windowSeal
  exact
    ⟨requestUnary, locatedUnary, cellUnary, windowUnary, sealUnary, requestLocated,
      cellWindow, windowSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.LocatednessModulusUp

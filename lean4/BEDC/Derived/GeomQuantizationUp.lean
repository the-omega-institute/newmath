import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GeomQuantizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeomQuantizationBHistSourcePacket [AskSetup] [PackageSetup]
    (symplectic hilbert lineBundle polarisation metaplectic contReadback transport endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory lineBundle ∧
    UnaryHistory polarisation ∧ UnaryHistory metaplectic ∧ UnaryHistory transport ∧
      Cont symplectic lineBundle polarisation ∧ Cont polarisation metaplectic contReadback ∧
        Cont contReadback hilbert endpoint ∧ PkgSig bundle endpoint pkg

end BEDC.Derived.GeomQuantizationUp

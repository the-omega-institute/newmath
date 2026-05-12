import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FreeMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FreeMonoidWordCarrier [AskSetup] [PackageSetup]
    (word route provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
    Cont word route provenance ∧ PkgSig bundle provenance pkg

theorem FreeMonoidWordCarrier_concat_associativity [AskSetup] [PackageSetup]
    {u v w uv left vw right route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier u route provenance bundle pkg ->
      FreeMonoidWordCarrier v route provenance bundle pkg ->
        FreeMonoidWordCarrier w route provenance bundle pkg ->
          Cont u v uv ->
            Cont uv w left ->
              Cont v w vw ->
                Cont u vw right ->
                  PkgSig bundle provenance pkg ->
                    hsame left right := by
  intro _uCarrier _vCarrier _wCarrier uvRow leftRow vwRow rightRow _pkgSig
  unfold Cont at uvRow leftRow vwRow rightRow
  cases uvRow
  cases leftRow
  cases vwRow
  cases rightRow
  exact append_assoc u v w

end BEDC.Derived.FreeMonoidUp

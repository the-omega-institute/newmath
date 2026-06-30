import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive StoneRepresentationBooleanAlgebraUp : Type where
  | mk (B U T L M H C P N : BHist) : StoneRepresentationBooleanAlgebraUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.StoneRepresentationBooleanAlgebraUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StoneRepresentationBooleanAlgebraCarrier_duality_handoff [AskSetup] [PackageSetup]
    {B U T L M H C P N stoneRead topologyRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B T stoneRead ->
      Cont stoneRead L topologyRead ->
        Cont topologyRead M regularRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              UnaryHistory B ->
                UnaryHistory T ->
                  UnaryHistory L ->
                    UnaryHistory M ->
                      UnaryHistory stoneRead ∧ UnaryHistory topologyRead ∧
                        UnaryHistory regularRead ∧ Cont B T stoneRead ∧
                          Cont stoneRead L topologyRead ∧ Cont topologyRead M regularRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro stoneRoute topologyRoute regularRoute provenancePkg localPkg bUnary tUnary lUnary mUnary
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed bUnary tUnary stoneRoute
  have topologyUnary : UnaryHistory topologyRead :=
    unary_cont_closed stoneUnary lUnary topologyRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed topologyUnary mUnary regularRoute
  exact
    ⟨stoneUnary, topologyUnary, regularUnary, stoneRoute, topologyRoute, regularRoute,
      provenancePkg, localPkg⟩

end BEDC.Derived.StoneRepresentationBooleanAlgebraUp

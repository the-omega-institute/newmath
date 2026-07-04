import BEDC.Derived.ChainableContinuumUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChainableContinuumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChainableContinuumCarrier_finite_chain_refinement [AskSetup] [PackageSetup]
    {K C L M T R H P N chainRead meshRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory C ->
        UnaryHistory L ->
          UnaryHistory M ->
            UnaryHistory T ->
              PkgSig bundle N pkg ->
                Cont K C chainRead ->
                  Cont L M meshRead ->
                    UnaryHistory chainRead ∧ UnaryHistory meshRead ∧
                      Cont K C chainRead ∧ Cont L M meshRead ∧ PkgSig bundle N pkg ∧
                        chainableContinuumFields
                            (ChainableContinuumUp.mk K C L M T R H P N) =
                          [K, C, L, M, T, R, H, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro unaryK unaryC unaryL unaryM _unaryT pkgN chainRoute meshRoute
  have chainUnary : UnaryHistory chainRead :=
    unary_cont_closed unaryK unaryC chainRoute
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed unaryL unaryM meshRoute
  exact ⟨chainUnary, meshUnary, chainRoute, meshRoute, pkgN, rfl⟩

theorem ChainableContinuumCarrier_nonescape [AskSetup] [PackageSetup]
    {K C L M T R H P N exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory C ->
        UnaryHistory L ->
          UnaryHistory M ->
            UnaryHistory T ->
              UnaryHistory R ->
                UnaryHistory H ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      Cont L M exported ->
                        UnaryHistory exported ∧ hsame exported exported ∧
                          Cont L M exported ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro _unaryK _unaryC unaryL unaryM _unaryT _unaryR _unaryH pkgP pkgN exportedRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed unaryL unaryM exportedRoute
  exact ⟨exportedUnary, hsame_refl exported, exportedRoute, pkgP, pkgN⟩

end BEDC.Derived.ChainableContinuumUp

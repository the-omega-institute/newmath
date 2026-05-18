import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_negative_row_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n refusal audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d) ->
        Cont h p audit ->
          PkgSig bundle audit pkg ->
            UnaryHistory refusal ∧ UnaryHistory audit ∧ Cont h p audit ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro packet refusalSurface auditRoute auditPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, _gUnary, _routeAB, _routeCD,
      routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed eUnary fUnary routeEF
  have refusalUnary : UnaryHistory refusal := by
    cases refusalSurface with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr sameD =>
                exact unary_transport_symm dUnary sameD
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed hUnary pUnary auditRoute
  exact
    ⟨refusalUnary, auditUnary, auditRoute, sameProvenanceName, provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp

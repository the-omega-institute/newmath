import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_negative_theorem_surface [AskSetup]
    [PackageSetup] {a b c d e f g h p n refusal audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d) →
        Cont h p audit →
          PkgSig bundle audit pkg →
            UnaryHistory refusal ∧ UnaryHistory audit ∧ Cont a b h ∧ Cont c d h ∧
              Cont h p audit ∧ hsame p n ∧ PkgSig bundle p pkg ∧
                PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg hsame Cont
  intro packet refusalSurface auditRoute auditPkg
  have refusalLedger :=
    AxisZeckendorfCannotClaimRegistryPacket_refusal_ledger_row packet
      (show
        hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d ∨
          hsame refusal e ∨ hsame refusal f ∨ hsame refusal g from by
          cases refusalSurface with
          | inl sameA =>
              exact Or.inl sameA
          | inr rest =>
              cases rest with
              | inl sameB =>
                  exact Or.inr (Or.inl sameB)
              | inr rest =>
                  cases rest with
                  | inl sameC =>
                      exact Or.inr (Or.inr (Or.inl sameC))
                  | inr sameD =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameD))))
  have publicBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_public_boundary packet auditRoute auditPkg
  obtain ⟨refusalUnary, routeAB, routeCD, _routeEF, sameProvenanceName, provenancePkg⟩ :=
    refusalLedger
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _hUnary,
      _pUnary, auditUnary, auditRoute', _sameProvenanceName', _provenancePkg',
      auditPkg'⟩ := publicBoundary
  exact
    ⟨refusalUnary, auditUnary, routeAB, routeCD, auditRoute', sameProvenanceName,
      provenancePkg, auditPkg'⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp

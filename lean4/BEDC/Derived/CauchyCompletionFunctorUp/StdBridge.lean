import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorUp_StdBridge [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont endpoint nameCert bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row regular ∨ hsame row sealRow ∨
                  hsame row monadRow ∨ hsame row universal ∨ hsame row classifier ∨
                    hsame row transport ∨ hsame row nameCert ∨ hsame row endpoint ∨
                      hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont metric regular sealRow ∧
                  Cont monadRow universal endpoint ∧ Cont classifier transport nameCert ∧
                    Cont endpoint nameCert bridgeRead ∧ PkgSig bundle bridgeRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet endpointNameBridge bridgePkg
  obtain ⟨_metricUnary, _regularUnary, _sealUnary, _monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, nameCertUnary, endpointUnary, metricRegularSeal,
    monadUniversalEndpoint, classifierTransportNameCert, _endpointPkg⟩ := packet
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary nameCertUnary endpointNameBridge
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceBridge
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, metricRegularSeal, monadUniversalEndpoint,
          classifierTransportNameCert, endpointNameBridge, bridgePkg⟩
  }

end BEDC.Derived.CauchyCompletionFunctorUp

import BEDC.Derived.CauchyfiltercompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionBridgeFacingInterface [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead
      sealRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont filter windows sourceRead ->
        Cont sourceRead tolerance sealRead ->
          Cont sealRead provenance bridgeRead ->
            PkgSig bundle bridgeRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                      hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                        hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                          hsame row bridgeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont filter windows sourceRead ∧
                      Cont sourceRead tolerance sealRead ∧ Cont sealRead provenance bridgeRead ∧
                        PkgSig bundle bridgeRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sourceRoute sealRoute bridgeRoute bridgePkg
  obtain ⟨filterUnary, _windowsUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary _windowsUnary sourceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary toleranceUnary sealRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sealReadUnary provenanceUnary bridgeRoute
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont filter windows sourceRead ∧
              Cont sourceRead tolerance sealRead ∧ Cont sealRead provenance bridgeRead ∧
                PkgSig bundle bridgeRead pkg)
          hsame := {
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
        intro row other sameRows source
        cases source with
        | intro sameBridge rowUnary =>
            exact
              ⟨hsame_trans (hsame_symm sameRows) sameBridge,
                unary_transport rowUnary sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, sealRoute, bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, sourceUnary, sealReadUnary, bridgeUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp

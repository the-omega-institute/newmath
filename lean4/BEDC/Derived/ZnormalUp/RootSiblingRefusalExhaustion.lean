import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootSiblingRefusalExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalwordRoute
      downstream hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalwordRoute →
        Cont normalwordRoute routes downstream →
          PkgSig bundle downstream pkg →
            SemanticNameCert
                (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row normal ∨ hsame row continuation ∨ hsame row normalwordRoute ∨
                    hsame row downstream)
                (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
                hsame ∧
              UnaryHistory normalwordRoute ∧ UnaryHistory downstream ∧
                Cont normal continuation normalwordRoute ∧
                  Cont normalwordRoute routes downstream ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle downstream pkg ∧
                      (Cont downstream (BHist.e0 hostTail) normal → False) ∧
                        (Cont downstream (BHist.e1 hostTail) normal → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationNormalword normalwordRoutesDownstream downstreamPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalwordUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalword
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalwordUnary routesUnary normalwordRoutesDownstream
  have downstreamSource :
      (fun row : BHist => hsame row downstream ∧ UnaryHistory row) downstream := by
    exact ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row normalwordRoute ∨
              hsame row downstream)
          (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream downstreamSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamPkg⟩
  }
  have normalToDownstream : Cont normal (append continuation routes) downstream := by
    cases normalContinuationNormalword
    cases normalwordRoutesDownstream
    exact append_assoc normal continuation routes
  have e0Refusal : Cont downstream (BHist.e0 hostTail) normal → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left normalToDownstream back
  have e1Refusal : Cont downstream (BHist.e1 hostTail) normal → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right normalToDownstream back
  exact
    ⟨cert, normalwordUnary, downstreamUnary, normalContinuationNormalword,
      normalwordRoutesDownstream, provenancePkg, downstreamPkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZnormalUp

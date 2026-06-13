import BEDC.Derived.RationalIntervalRefinementUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalRefinementChainExactness [AskSetup] [PackageSetup]
    {parent child endpoint retained support transport replay provenance localName nextChild
      chainRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier parent child endpoint retained support transport replay
        provenance localName bundle pkg ->
      Cont child endpoint nextChild ->
        Cont retained nextChild chainRead ->
          PkgSig bundle chainRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row chainRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row parent ∨ hsame row child ∨ hsame row endpoint ∨
                    hsame row retained ∨ hsame row nextChild ∨ hsame row chainRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont child endpoint nextChild ∧
                    Cont retained nextChild chainRead ∧ PkgSig bundle chainRead pkg)
                hsame ∧
              UnaryHistory nextChild ∧ UnaryHistory chainRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier childEndpointNext retainedNextChain chainReadPkg
  obtain ⟨_parentUnary, childUnary, endpointUnary, retainedUnary, _supportUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _parentChildEndpoint,
    _endpointRetainedSupport, _supportTransportReplay, _provenancePkg, _localNamePkg⟩ :=
      carrier
  have nextChildUnary : UnaryHistory nextChild :=
    unary_cont_closed childUnary endpointUnary childEndpointNext
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed retainedUnary nextChildUnary retainedNextChain
  have sourceChain :
      (fun row : BHist => hsame row chainRead ∧ UnaryHistory row) chainRead := by
    exact ⟨hsame_refl chainRead, chainReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row chainRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row parent ∨ hsame row child ∨ hsame row endpoint ∨
              hsame row retained ∨ hsame row nextChild ∨ hsame row chainRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont child endpoint nextChild ∧
              Cont retained nextChild chainRead ∧ PkgSig bundle chainRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro chainRead sourceChain
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, childEndpointNext, retainedNextChain, chainReadPkg⟩
  }
  exact ⟨cert, nextChildUnary, chainReadUnary⟩

end BEDC.Derived.RationalIntervalRefinementUp

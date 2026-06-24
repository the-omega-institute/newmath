import BEDC.Derived.CauchyEquivalenceSetoidUp.DownstreamEqualityDependency

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidSeparatedMetricFactorization [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead
      separatedMetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont test sealRow sealRead ->
        Cont sealRead provenance separatedMetricRead ->
          PkgSig bundle separatedMetricRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row separatedMetricRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                      hsame row separatedMetricRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont test sealRow sealRead ∧
                    Cont sealRead provenance separatedMetricRead ∧
                      PkgSig bundle separatedMetricRead pkg)
                hsame ∧
              UnaryHistory sealRead ∧ UnaryHistory separatedMetricRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute separatedMetricRoute separatedMetricPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _leftTransport, _rightReplay,
    _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have separatedMetricUnary : UnaryHistory separatedMetricRead :=
    unary_cont_closed sealReadUnary provenanceUnary separatedMetricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedMetricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row separatedMetricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead provenance separatedMetricRead ∧
                PkgSig bundle separatedMetricRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedMetricRead
        ⟨hsame_refl separatedMetricRead, separatedMetricUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, separatedMetricRoute, separatedMetricPkg⟩
  }
  exact ⟨cert, sealReadUnary, separatedMetricUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp

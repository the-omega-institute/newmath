import BEDC.Derived.CauchyEquivalenceSetoidUp

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidRealSeparabilityForwardAnchor [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead
      densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow sealRead →
        Cont sealRead replay equalityRead →
          Cont equalityRead provenance densityRead →
            PkgSig bundle equalityRead pkg →
              PkgSig bundle densityRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                        hsame row dyadic ∨ hsame row test ∨ hsame row sealRead ∨
                          hsame row equalityRead ∨ hsame row densityRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont test sealRow sealRead ∧
                        Cont sealRead replay equalityRead ∧
                          Cont equalityRead provenance densityRead ∧
                            PkgSig bundle densityRead pkg)
                    hsame ∧
                  UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier sealRoute equalityRoute densityRoute equalityPkg densityPkg
  have surface :
      UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
        UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
          UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧ Cont test sealRow sealRead ∧
            Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg :=
    CauchyEquivalenceSetoidNameCertSurface carrier sealRoute equalityRoute equalityPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, _testUnary,
    _sealUnary, _sealReadUnary, equalityUnary, _surfaceSealRoute, _surfaceEqualityRoute,
    _provenancePkg, _namePkg, _surfaceEqualityPkg⟩ := surface
  obtain ⟨_carrierS0Unary, _carrierS1Unary, _carrierR0Unary, _carrierR1Unary,
    _carrierDyadicUnary, _carrierTestUnary, _carrierSealUnary, _transportUnary,
    _replayUnary, provenanceUnary, _nameUnary, _leftTransport, _rightReplay,
    _dyadicSeal, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed equalityUnary provenanceUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRead ∨
                hsame row equalityRead ∨ hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead replay equalityRead ∧ Cont equalityRead provenance densityRead ∧
                PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, equalityRoute, densityRoute, densityPkg⟩
  }
  exact ⟨cert, densityUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp

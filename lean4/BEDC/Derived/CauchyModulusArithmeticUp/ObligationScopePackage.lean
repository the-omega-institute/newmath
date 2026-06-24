import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_obligation_scope_package [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName sumRead productRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic sumRead ->
        Cont meet dyadic productRead ->
          Cont sumRead productRead realSealRead ->
            PkgSig bundle realSealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row meet ∨ hsame row sumRead ∨ hsame row productRead ∨
                      hsame row sealRow ∨ hsame row realSealRead)
                  (fun row : BHist =>
                    hsame row realSealRead ∧ Cont meet dyadic sumRead ∧
                      Cont meet dyadic productRead ∧ Cont sumRead productRead realSealRead ∧
                        PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory sumRead ∧ UnaryHistory productRead ∧
                  UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sumRoute productRoute realSealRoute _realSealPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, dyadicUnary, _windowUnary, _readbackUnary, _sealRowUnary,
      _transportUnary, _meetRoute, _sumCarrierRoute, _productCarrierRoute, _windowRoute,
      _provenanceRoute, localPackage⟩ := carrier
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed meetUnary dyadicUnary sumRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed meetUnary dyadicUnary productRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed sumReadUnary productReadUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row meet ∨ hsame row sumRead ∨ hsame row productRead ∨
              hsame row sealRow ∨ hsame row realSealRead)
          (fun row : BHist =>
            hsame row realSealRead ∧ Cont meet dyadic sumRead ∧
              Cont meet dyadic productRead ∧ Cont sumRead productRead realSealRead ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSealRead
        ⟨hsame_refl realSealRead, realSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sumRoute, productRoute, realSealRoute, localPackage⟩
  }
  exact ⟨cert, sumReadUnary, productReadUnary, realSealUnary⟩

end BEDC.Derived.CauchyModulusArithmeticUp

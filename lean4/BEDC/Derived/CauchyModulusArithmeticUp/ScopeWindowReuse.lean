import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_scope_window_reuse [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName thresholdRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic thresholdRead ->
        Cont thresholdRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row window ∨ hsame row dyadic ∨ hsame row readback ∨
                    hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont meet dyadic thresholdRead ∧
                    Cont thresholdRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                UnaryHistory thresholdRead ∧ UnaryHistory sealRead ∧
                  Cont meet dyadic sum ∧ Cont meet dyadic product := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier thresholdRoute sealRoute sealPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, dyadicUnary, windowUnary, readbackUnary, sealRowUnary,
      _transportUnary, _meetRoute, sumRoute, productRoute, _windowSealRoute,
      _provenanceRoute, _localPackage⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed meetUnary dyadicUnary thresholdRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed thresholdUnary sealRowUnary sealRoute
  have sourceAtSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadic ∨ hsame row readback ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont meet dyadic thresholdRead ∧
              Cont thresholdRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceAtSeal
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdRoute, sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, windowUnary, dyadicUnary, readbackUnary, thresholdUnary, sealUnary, sumRoute,
      productRoute⟩

end BEDC.Derived.CauchyModulusArithmeticUp

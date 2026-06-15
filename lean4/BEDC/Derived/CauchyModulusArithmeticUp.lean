import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusArithmeticCarrier [AskSetup] [PackageSetup]
    (stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream0 ∧ UnaryHistory stream1 ∧ UnaryHistory modulus0 ∧
    UnaryHistory modulus1 ∧ UnaryHistory meet ∧ UnaryHistory sum ∧
      UnaryHistory product ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
          Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
            Cont meet dyadic product ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem CauchyModulusArithmeticCarrier_sum_meet_closure [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName sumProductRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product sumProductRead ->
        hsame transport (append meet dyadic) ->
          UnaryHistory meet ∧ UnaryHistory sum ∧ UnaryHistory product ∧
            UnaryHistory dyadic ∧ UnaryHistory sumProductRead ∧ Cont meet dyadic sum ∧
              Cont meet dyadic product ∧ Cont sum product sumProductRead ∧
                hsame transport (append meet dyadic) ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig
  intro carrier sumProductRoute transportAnchor
  cases carrier with
  | intro uStream0 rest =>
      cases rest with
      | intro uStream1 rest =>
          cases rest with
          | intro uModulus0 rest =>
              cases rest with
              | intro uModulus1 rest =>
                  cases rest with
                  | intro uMeet rest =>
                      cases rest with
                      | intro uSum rest =>
                          cases rest with
                          | intro uProduct rest =>
                              cases rest with
                              | intro uDyadic rest =>
                                  cases rest with
                                  | intro uWindow rest =>
                                      cases rest with
                                      | intro uReadback rest =>
                                          cases rest with
                                          | intro uSealRow rest =>
                                              cases rest with
                                              | intro uTransport rest =>
                                                  cases rest with
                                                  | intro moduliMeet rest =>
                                                      cases rest with
                                                      | intro meetDyadicSum rest =>
                                                          cases rest with
                                                          | intro meetDyadicProduct rest =>
                                                              cases rest with
                                                              | intro windowReadbackSeal rest =>
                                                                  cases rest with
                                                                  | intro transportReplayProvenance
                                                                      pkgSig =>
                                                                      constructor
                                                                      · exact uMeet
                                                                      · constructor
                                                                        · exact uSum
                                                                        · constructor
                                                                          · exact uProduct
                                                                          · constructor
                                                                            · exact uDyadic
                                                                            · constructor
                                                                              · exact
                                                                                  unary_cont_closed
                                                                                    uSum uProduct
                                                                                    sumProductRoute
                                                                              · constructor
                                                                                · exact meetDyadicSum
                                                                                · constructor
                                                                                  · exact meetDyadicProduct
                                                                                  · constructor
                                                                                    · exact
                                                                                        sumProductRoute
                                                                                    · constructor
                                                                                      · exact
                                                                                          transportAnchor
                                                                                      · exact pkgSig

theorem CauchyModulusArithmeticCarrier_sum_meet_route_closure [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic sumRead ->
        UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sum ∧ UnaryHistory sumRead ∧
          Cont meet dyadic sum ∧ Cont meet dyadic sumRead ∧ Cont window readback sealRow := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sumReadRoute
  exact
    match carrier with
    | ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
        sumUnary, _productUnary, dyadicUnary, _windowUnary, _readbackUnary, _sealUnary,
        _transportUnary, _meetRoute, sumRoute, _productRoute, windowRoute,
        _transportRoute, _pkgSig⟩ =>
        ⟨meetUnary, dyadicUnary, sumUnary, unary_cont_closed meetUnary dyadicUnary sumReadRoute,
          sumRoute, sumReadRoute, windowRoute⟩

theorem CauchyModulusArithmeticCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream0 ∨ hsame row stream1 ∨ hsame row meet ∨ hsame row sum ∨
              hsame row product ∨ hsame row sealRow)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame ∧
        Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧ Cont meet dyadic product ∧
          Cont window readback sealRow ∧ Cont transport replay provenance ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, _windowUnary, _readbackUnary,
      sealUnary, _transportUnary, meetRoute, sumRoute, productRoute, sealRoute,
      provenanceRoute, packageRoute⟩ := carrier
  have sourceAtSeal : hsame sealRow sealRow ∧ UnaryHistory sealRow :=
    ⟨hsame_refl sealRow, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream0 ∨ hsame row stream1 ∨ hsame row meet ∨ hsame row sum ∨
              hsame row product ∨ hsame row sealRow)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
        have otherSameSeal : hsame _other sealRow :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory _other := by
          cases sameRows
          exact source.right
        exact ⟨otherSameSeal, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute, provenanceRoute, packageRoute⟩
  }
  exact ⟨cert, meetRoute, sumRoute, productRoute, sealRoute, provenanceRoute, packageRoute⟩

theorem CauchyModulusArithmeticCarrier_product_tail_bound [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName productTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
      window readback sealRow transport replay provenance localName bundle pkg →
    Cont product window productTail →
    PkgSig bundle productTail pkg →
    UnaryHistory product ∧ UnaryHistory window ∧ UnaryHistory productTail ∧
      Cont product window productTail ∧ PkgSig bundle localName pkg ∧
        PkgSig bundle productTail pkg := by
  intro carrier productRoute productPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      _sumUnary, productUnary, _dyadicUnary, windowUnary, _readbackUnary,
      _sealUnary, _transportUnary, _meetRoute, _sumRoute, _carrierProductRoute,
      _sealRoute, _provenanceRoute, localPackage⟩ := carrier
  exact
    ⟨productUnary, windowUnary, unary_cont_closed productUnary windowUnary productRoute,
      productRoute, localPackage, productPackage⟩

theorem CauchyModulusArithmeticCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
      window readback sealRow transport replay provenance localName bundle pkg →
    Cont window readback sealRow ∧ Cont transport replay provenance ∧
      PkgSig bundle localName pkg ∧ UnaryHistory sealRow := by
  intro carrier
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, _windowUnary, _readbackUnary,
      sealUnary, _transportUnary, _meetRoute, _sumRoute, _productRoute, sealRoute,
      provenanceRoute, localPackage⟩ := carrier
  exact ⟨sealRoute, provenanceRoute, localPackage, sealUnary⟩

end BEDC.Derived.CauchyModulusArithmeticUp

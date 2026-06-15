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

theorem CauchyModulusArithmeticCarrier_namecert_obligation_carrier [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      UnaryHistory stream0 /\ UnaryHistory stream1 /\ UnaryHistory modulus0 /\
        UnaryHistory modulus1 /\ UnaryHistory meet /\ UnaryHistory sum /\
          UnaryHistory product /\ UnaryHistory dyadic /\ UnaryHistory window /\
            UnaryHistory readback /\ UnaryHistory sealRow /\ UnaryHistory transport /\
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier
  obtain
    ⟨stream0Unary, stream1Unary, modulus0Unary, modulus1Unary, meetUnary, sumUnary,
      productUnary, dyadicUnary, windowUnary, readbackUnary, sealUnary, transportUnary,
      _meetRoute, _sumRoute, _productRoute, _sealRoute, _provenanceRoute,
      packageRoute⟩ := carrier
  exact
    ⟨stream0Unary, stream1Unary, modulus0Unary, modulus1Unary, meetUnary, sumUnary,
      productUnary, dyadicUnary, windowUnary, readbackUnary, sealUnary, transportUnary,
      packageRoute⟩

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

theorem CauchyModulusArithmeticCarrier_real_consumer_boundary [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName sumProductRead productTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product sumProductRead ->
        Cont product window productTail ->
          PkgSig bundle productTail pkg ->
            UnaryHistory sum /\ UnaryHistory product /\ UnaryHistory window /\
              UnaryHistory sumProductRead /\ UnaryHistory productTail /\
                Cont sum product sumProductRead /\ Cont product window productTail /\
                  Cont window readback sealRow /\ PkgSig bundle localName pkg /\
                    PkgSig bundle productTail pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier sumProductRoute productTailRoute productTailPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      sumUnary, productUnary, _dyadicUnary, windowUnary, _readbackUnary, _sealUnary,
      _transportUnary, _meetRoute, _sumRoute, _carrierProductRoute, sealRoute,
      _provenanceRoute, localPackage⟩ := carrier
  exact
    ⟨sumUnary, productUnary, windowUnary,
      unary_cont_closed sumUnary productUnary sumProductRoute,
      unary_cont_closed productUnary windowUnary productTailRoute,
      sumProductRoute, productTailRoute, sealRoute, localPackage, productTailPackage⟩

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

theorem CauchyModulusArithmeticCarrier_shared_threshold_totality [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg →
      Cont meet dyadic thresholdRead →
        PkgSig bundle thresholdRead pkg →
          UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sum ∧
            UnaryHistory product ∧ UnaryHistory thresholdRead ∧ Cont meet dyadic sum ∧
              Cont meet dyadic product ∧ Cont meet dyadic thresholdRead ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle thresholdRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier thresholdRoute thresholdPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, _windowUnary, _readbackUnary,
      _sealUnary, _transportUnary, _meetRoute, sumRoute, productRoute, _sealRoute,
      _provenanceRoute, localPackage⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed meetUnary dyadicUnary thresholdRoute
  exact
    ⟨meetUnary, dyadicUnary, sumUnary, productUnary, thresholdUnary, sumRoute,
      productRoute, thresholdRoute, localPackage, thresholdPkg⟩

theorem CauchyModulusArithmeticCarrier_common_tail_window [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName tailWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont modulus0 meet tailWindow ->
        UnaryHistory modulus0 ∧ UnaryHistory modulus1 ∧ UnaryHistory meet ∧
          UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory tailWindow ∧
            Cont modulus0 meet tailWindow ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier tailRoute
  obtain
    ⟨_stream0Unary, _stream1Unary, modulus0Unary, modulus1Unary, meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, windowUnary, readbackUnary,
      _sealUnary, _transportUnary, _meetRoute, _sumRoute, _productRoute, sealRoute,
      provenanceRoute, packageRoute⟩ := carrier
  exact
    ⟨modulus0Unary, modulus1Unary, meetUnary, windowUnary, readbackUnary,
      unary_cont_closed modulus0Unary meetUnary tailRoute, tailRoute, sealRoute,
      provenanceRoute, packageRoute⟩

theorem CauchyModulusArithmeticCarrier_diagonal_dominates_sum_product [AskSetup]
    [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName diagonalRead sumRead productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic diagonalRead ->
        Cont diagonalRead sum sumRead ->
          Cont diagonalRead product productRead ->
            PkgSig bundle productRead pkg ->
              UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory diagonalRead ∧
                UnaryHistory sumRead ∧ UnaryHistory productRead ∧ Cont meet dyadic
                  diagonalRead ∧ Cont diagonalRead sum sumRead ∧
                    Cont diagonalRead product productRead ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle productRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier diagonalRoute sumRoute productRoute productPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, _windowUnary, _readbackUnary, _sealUnary,
      _transportUnary, _meetRoute, _sumCarrierRoute, _productCarrierRoute,
      _sealRoute, _provenanceRoute, localPkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed meetUnary dyadicUnary diagonalRoute
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed diagonalUnary sumUnary sumRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed diagonalUnary productUnary productRoute
  exact
    ⟨meetUnary, dyadicUnary, diagonalUnary, sumReadUnary, productReadUnary,
      diagonalRoute, sumRoute, productRoute, localPkg, productPkg⟩

theorem CauchyModulusArithmeticCarrier_uniform_product_budget [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName productTail productBudget realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont product window productTail ->
        Cont productTail readback productBudget ->
          Cont productBudget sealRow realSealRead ->
            PkgSig bundle realSealRead pkg ->
              UnaryHistory productTail ∧ UnaryHistory productBudget ∧
                UnaryHistory realSealRead ∧ Cont product window productTail ∧
                  Cont productTail readback productBudget ∧
                    Cont productBudget sealRow realSealRead ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier productRoute budgetRoute sealRoute realSealPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      _sumUnary, productUnary, _dyadicUnary, windowUnary, readbackUnary,
      sealUnary, _transportUnary, _meetRoute, _sumCarrierRoute, _productCarrierRoute,
      _sealCarrierRoute, _provenanceRoute, localPkg⟩ := carrier
  have productTailUnary : UnaryHistory productTail :=
    unary_cont_closed productUnary windowUnary productRoute
  have productBudgetUnary : UnaryHistory productBudget :=
    unary_cont_closed productTailUnary readbackUnary budgetRoute
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed productBudgetUnary sealUnary sealRoute
  exact
    ⟨productTailUnary, productBudgetUnary, realSealReadUnary, productRoute, budgetRoute,
      sealRoute, localPkg, realSealPkg⟩

theorem CauchyModulusArithmeticCarrier_real_seal_modulus_nonescape
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName modulusRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic modulusRead ->
        Cont modulusRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sealRow ∧
              UnaryHistory modulusRead ∧ UnaryHistory sealRead ∧
                Cont meet dyadic modulusRead ∧ Cont modulusRead sealRow sealRead ∧
                  Cont window readback sealRow ∧ Cont transport replay provenance ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier modulusRoute sealReadRoute sealReadPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, dyadicUnary, _windowUnary, _readbackUnary, sealRowUnary,
      _transportUnary, _meetRoute, _sumRoute, _productRoute, windowReadbackSeal,
      transportReplayProvenance, localPackage⟩ := carrier
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed meetUnary dyadicUnary modulusRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusReadUnary sealRowUnary sealReadRoute
  exact
    ⟨meetUnary, dyadicUnary, sealRowUnary, modulusReadUnary, sealReadUnary, modulusRoute,
      sealReadRoute, windowReadbackSeal, transportReplayProvenance, localPackage,
      sealReadPackage⟩

theorem CauchyModulusArithmeticCarrier_product_meet_compatibility
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic productRead ->
        UnaryHistory modulus0 ∧ UnaryHistory modulus1 ∧ UnaryHistory meet ∧
          UnaryHistory dyadic ∧ UnaryHistory product ∧ UnaryHistory productRead ∧
            Cont modulus0 modulus1 meet ∧ Cont meet dyadic product ∧
              Cont meet dyadic productRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier productReadRoute
  obtain
    ⟨_stream0Unary, _stream1Unary, modulus0Unary, modulus1Unary, meetUnary,
      _sumUnary, productUnary, dyadicUnary, _windowUnary, _readbackUnary,
      _sealUnary, _transportUnary, meetRoute, _sumRoute, productRoute, _sealRoute,
      _provenanceRoute, packageRoute⟩ := carrier
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed meetUnary dyadicUnary productReadRoute
  exact
    ⟨modulus0Unary, modulus1Unary, meetUnary, dyadicUnary, productUnary,
      productReadUnary, meetRoute, productRoute, productReadRoute, packageRoute⟩

end BEDC.Derived.CauchyModulusArithmeticUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalModulusPacket [AskSetup] [PackageSetup]
    (precision threshold window readback ledger «seal» provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory window ∧
    Cont precision threshold window ∧ Cont window readback ledger ∧
      Cont ledger «seal» provenance ∧ PkgSig bundle provenance pkg ∧ UnaryHistory nameCert

theorem DiagonalModulusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold window readback ledger «seal» provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalModulusPacket precision threshold window readback ledger «seal» provenance nameCert
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row «seal» ∧
              DiagonalModulusPacket precision threshold window readback ledger «seal» provenance
                nameCert bundle pkg)
          (fun row : BHist => hsame row «seal»)
          (fun row : BHist => hsame row «seal» ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory window ∧
          Cont precision threshold window ∧ Cont window readback ledger ∧
            Cont ledger «seal» provenance ∧ PkgSig bundle provenance pkg := by
  intro packet
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.left
  have precisionThresholdWindow : Cont precision threshold window :=
    packet.right.right.right.left
  have windowReadbackLedger : Cont window readback ledger :=
    packet.right.right.right.right.left
  have ledgerSealProvenance : Cont ledger «seal» provenance :=
    packet.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.left
  have sourceSeal :
      (fun row : BHist =>
        hsame row «seal» ∧
          DiagonalModulusPacket precision threshold window readback ledger «seal» provenance
            nameCert bundle pkg) «seal» := by
    exact ⟨hsame_refl «seal», packet⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row «seal» ∧
            DiagonalModulusPacket precision threshold window readback ledger «seal» provenance
              nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro «seal» sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        constructor
        · exact hsame_trans (hsame_symm same) source.left
        · exact source.right
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row «seal» ∧
              DiagonalModulusPacket precision threshold window readback ledger «seal» provenance
                nameCert bundle pkg)
          (fun row : BHist => hsame row «seal»)
          (fun row : BHist => hsame row «seal» ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact source.left
      ledger_sound := by
        intro row source
        exact ⟨source.left, pkgSig⟩
    }
  exact
    ⟨cert,
      precisionUnary,
      thresholdUnary,
      windowUnary,
      precisionThresholdWindow,
      windowReadbackLedger,
      ledgerSealProvenance,
      pkgSig⟩

theorem DiagonalModulusPacket_window_selector_total [AskSetup] [PackageSetup]
    {precision threshold window readback ledger sealRow provenance nameCert selector regseqRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalModulusPacket precision threshold window readback ledger sealRow provenance nameCert
        bundle pkg ->
      Cont precision threshold selector ->
        Cont selector window regseqRead ->
          PkgSig bundle regseqRead pkg ->
            UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory window ∧
              UnaryHistory selector ∧ UnaryHistory regseqRead ∧
                Cont precision threshold selector ∧ Cont selector window regseqRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg := by
  intro packet precisionThresholdSelector selectorWindowRead regseqPkg
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.left
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed precisionUnary thresholdUnary precisionThresholdSelector
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed selectorUnary windowUnary selectorWindowRead
  exact
    ⟨precisionUnary, thresholdUnary, windowUnary, selectorUnary, regseqUnary,
      precisionThresholdSelector, selectorWindowRead, provenancePkg, regseqPkg⟩

def DiagonalModulusWindowCarrier [AskSetup] [PackageSetup]
    (precision modulus window readback dyadic «seal» provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory readback ∧
    UnaryHistory dyadic ∧ UnaryHistory nameCert ∧ Cont precision modulus window ∧
      Cont window readback «seal» ∧ Cont readback dyadic provenance ∧
        PkgSig bundle «seal» pkg

theorem DiagonalModulusWindowCarrier_selector_total [AskSetup] [PackageSetup]
    {precision modulus window readback dyadic «seal» provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalModulusWindowCarrier precision modulus window readback dyadic «seal» provenance
        nameCert bundle pkg ->
      UnaryHistory window ∧ UnaryHistory «seal» ∧ hsame window (append precision modulus) ∧
        Cont window readback «seal» ∧ PkgSig bundle «seal» pkg := by
  intro carrier
  obtain ⟨precisionUnary, modulusUnary, readbackUnary, _dyadicUnary, _nameCertUnary,
    windowRow, sealRow, _provenanceRow, sealPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed precisionUnary modulusUnary windowRow
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed windowUnary readbackUnary sealRow
  exact ⟨windowUnary, sealUnary, windowRow, sealRow, sealPkg⟩

theorem DiagonalModulusWindowCarrier_completion_classifier_transport [AskSetup] [PackageSetup]
    {precision modulus window readback dyadic sealRow provenance nameCert precision' modulus'
      window' readback' dyadic' sealRow' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalModulusWindowCarrier precision modulus window readback dyadic sealRow provenance
        nameCert bundle pkg ->
      hsame precision precision' ->
        hsame modulus modulus' ->
          hsame window window' ->
            hsame readback readback' ->
              hsame dyadic dyadic' ->
                hsame sealRow sealRow' ->
                  hsame provenance provenance' ->
                    hsame nameCert nameCert' ->
                      PkgSig bundle sealRow' pkg ->
                        DiagonalModulusWindowCarrier precision' modulus' window' readback'
                          dyadic' sealRow' provenance' nameCert' bundle pkg := by
  intro carrier samePrecision sameModulus sameWindow sameReadback sameDyadic sameSeal
    sameProvenance sameNameCert sealPkg'
  obtain ⟨precisionUnary, modulusUnary, readbackUnary, dyadicUnary, nameCertUnary,
    precisionModulusWindow, windowReadbackSeal, readbackDyadicProvenance, _sealPkg⟩ := carrier
  exact
    ⟨unary_transport precisionUnary samePrecision,
      unary_transport modulusUnary sameModulus,
      unary_transport readbackUnary sameReadback,
      unary_transport dyadicUnary sameDyadic,
      unary_transport nameCertUnary sameNameCert,
      cont_hsame_transport samePrecision sameModulus sameWindow precisionModulusWindow,
      cont_hsame_transport sameWindow sameReadback sameSeal windowReadbackSeal,
      cont_hsame_transport sameReadback sameDyadic sameProvenance readbackDyadicProvenance,
      sealPkg'⟩

end BEDC.Derived.DiagonalModulusUp

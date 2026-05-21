import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLimitModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitModulusPacket [AskSetup] [PackageSetup]
    (input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory precision ∧
    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont input modulus threshold ∧
      Cont threshold precision window ∧ Cont window readback dyadicLedger ∧
        Cont dyadicLedger sealRow cert ∧ PkgSig bundle provenance pkg

theorem RegularCauchyLimitModulusPacket_classifier_transport_exactness [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert
      threshold' window' dyadicLedger' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      hsame threshold threshold' ->
        Cont input modulus threshold' ->
          Cont threshold' precision window' ->
            Cont window' readback dyadicLedger' ->
              Cont dyadicLedger' sealRow cert' ->
                RegularCauchyLimitModulusPacket input modulus precision threshold' window'
                  readback dyadicLedger' sealRow provenance cert' bundle pkg ∧
                  hsame window window' ∧ hsame dyadicLedger dyadicLedger' ∧
                    hsame cert cert' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameThreshold inputModulusThreshold' thresholdPrecisionWindow'
    windowReadbackLedger' ledgerSealCert'
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealUnary, provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackLedger, ledgerSealCert,
    provenancePkg⟩ := packet
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameThreshold (hsame_refl precision) thresholdPrecisionWindow
      thresholdPrecisionWindow'
  have sameLedger : hsame dyadicLedger dyadicLedger' :=
    cont_respects_hsame sameWindow (hsame_refl readback) windowReadbackLedger
      windowReadbackLedger'
  have sameCert : hsame cert cert' :=
    cont_respects_hsame sameLedger (hsame_refl sealRow) ledgerSealCert ledgerSealCert'
  have transported :
      RegularCauchyLimitModulusPacket input modulus precision threshold' window' readback
        dyadicLedger' sealRow provenance cert' bundle pkg := by
    exact ⟨inputUnary, modulusUnary, precisionUnary, sealUnary, provenanceUnary,
      inputModulusThreshold', thresholdPrecisionWindow', windowReadbackLedger',
      ledgerSealCert', provenancePkg⟩
  exact ⟨transported, sameWindow, sameLedger, sameCert⟩

theorem RegularCauchyLimitModulusPacket_diagonal_totality [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      UnaryHistory readback ->
        UnaryHistory threshold ∧ UnaryHistory window ∧ UnaryHistory dyadicLedger ∧
          UnaryHistory cert ∧ Cont input modulus threshold ∧ Cont threshold precision window ∧
            Cont window readback dyadicLedger ∧ Cont dyadicLedger sealRow cert ∧
              PkgSig bundle provenance pkg := by
  intro packet readbackUnary
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealRowUnary, _provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackDyadicLedger,
    dyadicLedgerSealRowCert, provenancePkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed inputUnary modulusUnary inputModulusThreshold
  have windowUnary : UnaryHistory window :=
    unary_cont_closed thresholdUnary precisionUnary thresholdPrecisionWindow
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadicLedger
  have certUnary : UnaryHistory cert :=
    unary_cont_closed dyadicLedgerUnary sealRowUnary dyadicLedgerSealRowCert
  exact
    ⟨thresholdUnary, windowUnary, dyadicLedgerUnary, certUnary, inputModulusThreshold,
      thresholdPrecisionWindow, windowReadbackDyadicLedger, dyadicLedgerSealRowCert,
      provenancePkg⟩

theorem RegularCauchyLimitModulusPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      UnaryHistory readback ->
        UnaryHistory sealRow ∧ UnaryHistory cert ∧ Cont window readback dyadicLedger ∧
          Cont dyadicLedger sealRow cert ∧ hsame cert (append dyadicLedger sealRow) ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet readbackUnary
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealRowUnary, provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackDyadicLedger,
    dyadicLedgerSealRowCert, provenancePkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed inputUnary modulusUnary inputModulusThreshold
  have windowUnary : UnaryHistory window :=
    unary_cont_closed thresholdUnary precisionUnary thresholdPrecisionWindow
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadicLedger
  have certUnary : UnaryHistory cert :=
    unary_cont_closed dyadicLedgerUnary sealRowUnary dyadicLedgerSealRowCert
  exact
    ⟨sealRowUnary, certUnary, windowReadbackDyadicLedger, dyadicLedgerSealRowCert,
      dyadicLedgerSealRowCert, provenancePkg⟩

theorem RegularCauchyLimitModulusNamecertObligations [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      UnaryHistory readback ->
        SemanticNameCert
            (fun row : BHist => hsame row cert ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row threshold ∨ hsame row window ∨ hsame row dyadicLedger ∨
                hsame row cert)
            (fun row : BHist => hsame row cert ∧ PkgSig bundle provenance pkg)
            hsame ∧
          UnaryHistory threshold ∧ UnaryHistory window ∧ UnaryHistory dyadicLedger ∧
            UnaryHistory cert ∧ Cont input modulus threshold ∧
              Cont threshold precision window ∧ Cont window readback dyadicLedger ∧
                Cont dyadicLedger sealRow cert ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet readbackUnary
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealRowUnary, _provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackDyadicLedger,
    dyadicLedgerSealRowCert, provenancePkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed inputUnary modulusUnary inputModulusThreshold
  have windowUnary : UnaryHistory window :=
    unary_cont_closed thresholdUnary precisionUnary thresholdPrecisionWindow
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadicLedger
  have certUnary : UnaryHistory cert :=
    unary_cont_closed dyadicLedgerUnary sealRowUnary dyadicLedgerSealRowCert
  have sourceCert :
      (fun row : BHist => hsame row cert ∧ UnaryHistory row) cert := by
    exact ⟨hsame_refl cert, certUnary⟩
  have certRows :
      SemanticNameCert
          (fun row : BHist => hsame row cert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row threshold ∨ hsame row window ∨ hsame row dyadicLedger ∨
              hsame row cert)
          (fun row : BHist => hsame row cert ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cert sourceCert
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
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨certRows, thresholdUnary, windowUnary, dyadicLedgerUnary, certUnary,
      inputModulusThreshold, thresholdPrecisionWindow, windowReadbackDyadicLedger,
      dyadicLedgerSealRowCert, provenancePkg⟩

end BEDC.Derived.RegularCauchyLimitModulusUp

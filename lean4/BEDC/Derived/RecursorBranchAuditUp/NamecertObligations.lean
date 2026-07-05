import BEDC.Derived.RecursorBranchAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RecursorBranchAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RecursorBranchAudit_namecert_obligations [AskSetup] [PackageSetup]
    {inductiveName signature recursor motive branches descent output transport replay
      provenance localName signatureRead branchRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory inductiveName ->
      UnaryHistory signature ->
        UnaryHistory recursor ->
          UnaryHistory motive ->
            UnaryHistory branches ->
              UnaryHistory descent ->
                UnaryHistory output ->
                  UnaryHistory transport ->
                    UnaryHistory replay ->
                      UnaryHistory provenance ->
                        UnaryHistory localName ->
                          Cont inductiveName signature signatureRead ->
                            Cont signatureRead branches branchRead ->
                              Cont branchRead descent descentRead ->
                                Cont descentRead output outputRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle localName pkg ->
                                      PkgSig bundle outputRead pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row outputRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row inductiveName ∨
                                                hsame row signature ∨
                                                  hsame row recursor ∨
                                                    hsame row motive ∨
                                                      hsame row branches ∨
                                                        hsame row descent ∨
                                                          hsame row outputRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont inductiveName signature signatureRead ∧
                                                  Cont signatureRead branches branchRead ∧
                                                    Cont branchRead descent descentRead ∧
                                                      Cont descentRead output outputRead ∧
                                                        PkgSig bundle outputRead pkg)
                                            hsame ∧
                                          UnaryHistory signatureRead ∧
                                            UnaryHistory branchRead ∧
                                              UnaryHistory descentRead ∧
                                                UnaryHistory outputRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro inductiveUnary signatureUnary _recursorUnary _motiveUnary branchesUnary descentUnary
    outputUnary _transportUnary _replayUnary _provenanceUnary _localNameUnary signatureRoute
    branchRoute descentRoute outputRoute _provenancePkg _localNamePkg outputPkg
  have signatureReadUnary : UnaryHistory signatureRead :=
    unary_cont_closed inductiveUnary signatureUnary signatureRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureReadUnary branchesUnary branchRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary outputRoute
  have sourceAtOutput :
      (fun row : BHist => hsame row outputRead ∧ UnaryHistory row) outputRead :=
    And.intro (hsame_refl outputRead) outputReadUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row inductiveName ∨ hsame row signature ∨ hsame row recursor ∨
            hsame row motive ∨ hsame row branches ∨ hsame row descent ∨
              hsame row outputRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont inductiveName signature signatureRead ∧
            Cont signatureRead branches branchRead ∧ Cont branchRead descent descentRead ∧
              Cont descentRead output outputRead ∧ PkgSig bundle outputRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead sourceAtOutput
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
        intro _row _other sameRows sourceRow
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.right
        (And.intro signatureRoute
          (And.intro branchRoute
            (And.intro descentRoute (And.intro outputRoute outputPkg))))
  }
  exact
    And.intro cert
      (And.intro signatureReadUnary
        (And.intro branchReadUnary (And.intro descentReadUnary outputReadUnary)))

theorem RecursorBranchAudit_namecert_eventflow_readback [AskSetup] [PackageSetup]
    {inductiveName signature recursor motive branches descent output transport replay
      provenance localName signatureRead branchRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory inductiveName ->
      UnaryHistory signature ->
        UnaryHistory recursor ->
          UnaryHistory motive ->
            UnaryHistory branches ->
              UnaryHistory descent ->
                UnaryHistory output ->
                  UnaryHistory transport ->
                    UnaryHistory replay ->
                      UnaryHistory provenance ->
                        UnaryHistory localName ->
                          Cont inductiveName signature signatureRead ->
                            Cont signatureRead branches branchRead ->
                              Cont branchRead descent descentRead ->
                                Cont descentRead output outputRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle localName pkg ->
                                      PkgSig bundle outputRead pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row outputRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row inductiveName ∨
                                                hsame row signature ∨
                                                  hsame row recursor ∨
                                                    hsame row motive ∨
                                                      hsame row branches ∨
                                                        hsame row descent ∨
                                                          hsame row outputRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont inductiveName signature signatureRead ∧
                                                  Cont signatureRead branches branchRead ∧
                                                    Cont branchRead descent descentRead ∧
                                                      Cont descentRead output outputRead ∧
                                                        PkgSig bundle outputRead pkg)
                                            hsame ∧
                                          recursorBranchAuditFromEventFlow
                                              (recursorBranchAuditToEventFlow
                                                (RecursorBranchAuditUp.mk inductiveName
                                                  signature recursor motive branches descent
                                                  output transport replay provenance localName)) =
                                            some
                                              (RecursorBranchAuditUp.mk inductiveName
                                                signature recursor motive branches descent output
                                                transport replay provenance localName) ∧
                                            (∀ y : RecursorBranchAuditUp,
                                              recursorBranchAuditFields
                                                  (RecursorBranchAuditUp.mk inductiveName
                                                    signature recursor motive branches descent
                                                    output transport replay provenance localName) =
                                                recursorBranchAuditFields y →
                                                  RecursorBranchAuditUp.mk inductiveName
                                                      signature recursor motive branches descent
                                                      output transport replay provenance localName =
                                                    y) ∧
                                              (∃ x y : RecursorBranchAuditUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert RecursorBranchAuditUp
  intro inductiveUnary signatureUnary recursorUnary motiveUnary branchesUnary descentUnary
    outputUnary transportUnary replayUnary provenanceUnary localNameUnary signatureRoute
    branchRoute descentRoute outputRoute provenancePkg localNamePkg outputPkg
  have obligations :=
    RecursorBranchAudit_namecert_obligations
      (inductiveName := inductiveName)
      (signature := signature)
      (recursor := recursor)
      (motive := motive)
      (branches := branches)
      (descent := descent)
      (output := output)
      (transport := transport)
      (replay := replay)
      (provenance := provenance)
      (localName := localName)
      (signatureRead := signatureRead)
      (branchRead := branchRead)
      (descentRead := descentRead)
      (outputRead := outputRead)
      (bundle := bundle)
      (pkg := pkg)
      inductiveUnary signatureUnary recursorUnary motiveUnary branchesUnary descentUnary
      outputUnary transportUnary replayUnary provenanceUnary localNameUnary signatureRoute
      branchRoute descentRoute outputRoute provenancePkg localNamePkg outputPkg
  have alignment := RecursorBranchAuditTasteGate_single_carrier_alignment
  exact
    And.intro obligations.left
      (And.intro
        (alignment.right.left
          (RecursorBranchAuditUp.mk inductiveName signature recursor motive branches descent
            output transport replay provenance localName))
        (And.intro
          (fun y fields =>
            alignment.right.right.right.right.left
              (RecursorBranchAuditUp.mk inductiveName signature recursor motive branches descent
                output transport replay provenance localName)
              y fields)
          alignment.right.right.right.right.right))

end BEDC.Derived.RecursorBranchAuditUp

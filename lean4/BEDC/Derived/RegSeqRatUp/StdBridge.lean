import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatUp_StdBridge [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback endpoint' regularity'
      readback' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      hsame endpoint endpoint' ->
        Cont endpoint' radius regularity' ->
          Cont regularity' provenance readback' ->
            PkgSig bundle readback' pkg ->
              (RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance
                    readback' bundle pkg ∧
                  hsame regularity regularity' ∧ hsame readback readback') ∧
                SemanticNameCert
                  (fun row : BHist => hsame row readback' ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row endpoint' ∨ hsame row regularity' ∨ hsame row readback' ∨
                      Cont regularity' provenance readback')
                  (fun row : BHist => PkgSig bundle readback' pkg ∧ hsame row readback')
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sameEndpoint targetRegularity targetReadback targetPkg
  have handoff :
      RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance readback'
          bundle pkg ∧
        hsame regularity regularity' ∧ hsame readback readback' :=
    RegSeqRatStreamCarrier_real_seal_handoff carrier sameEndpoint targetRegularity targetReadback
      targetPkg
  have readbackUnary' : UnaryHistory readback' :=
    handoff.left.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback' ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint' ∨ hsame row regularity' ∨ hsame row readback' ∨
              Cont regularity' provenance readback')
          (fun row : BHist => PkgSig bundle readback' pkg ∧ hsame row readback')
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback' ⟨hsame_refl readback', readbackUnary'⟩
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨targetPkg, source.left⟩
  }
  exact ⟨handoff, cert⟩

end BEDC.Derived.RegSeqRatUp

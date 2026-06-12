import BEDC.Derived.TypingJudgmentClassifierUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.TypingJudgmentClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem TypingJudgmentClassifierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {judgment membership derivation sigReadback contReplay transport provenance localName
      acceptedRead : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Ext judgment mark membership →
      Cont membership derivation contReplay →
        SigRel bundle judgment sigReadback →
          Cont sigReadback contReplay acceptedRead →
            PkgSig bundle provenance pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row acceptedRead)
                  (fun row : BHist =>
                    hsame row judgment ∨ hsame row membership ∨ hsame row derivation ∨
                      hsame row sigReadback ∨ hsame row contReplay ∨ hsame row transport ∨
                        hsame row provenance ∨ hsame row localName ∨ hsame row acceptedRead)
                  (fun row : BHist =>
                    hsame row acceptedRead ∧ Ext judgment mark membership ∧
                      Cont membership derivation contReplay ∧
                        SigRel bundle judgment sigReadback ∧
                          Cont sigReadback contReplay acceptedRead ∧
                            PkgSig bundle provenance pkg)
                  hsame ∧
                hsame acceptedRead acceptedRead := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle Pkg SemanticNameCert hsame
  intro membershipExt derivationRoute readbackSig replayRoute provenancePkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row acceptedRead)
          (fun row : BHist =>
            hsame row judgment ∨ hsame row membership ∨ hsame row derivation ∨
              hsame row sigReadback ∨ hsame row contReplay ∨ hsame row transport ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row acceptedRead)
          (fun row : BHist =>
            hsame row acceptedRead ∧ Ext judgment mark membership ∧
              Cont membership derivation contReplay ∧ SigRel bundle judgment sigReadback ∧
                Cont sigReadback contReplay acceptedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptedRead (hsame_refl acceptedRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr source)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source, membershipExt, derivationRoute, readbackSig, replayRoute, provenancePkg⟩
  }
  exact ⟨cert, hsame_refl acceptedRead⟩

end BEDC.Derived.TypingJudgmentClassifierUp

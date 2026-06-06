import BEDC.Derived.CauchyOscillationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationTailWindowAuditPackage [AskSetup] [PackageSetup]
    {W M Q T S H C P N windowRead thresholdRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M windowRead ->
        Cont windowRead Q thresholdRead ->
          Cont thresholdRead T ledgerRead ->
            Cont ledgerRead N namedRead ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W M windowRead ∧
                        Cont windowRead Q thresholdRead ∧
                          Cont thresholdRead T ledgerRead ∧ Cont ledgerRead N namedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier windowRoute thresholdRoute ledgerRoute namedRoute namedPkg
  obtain ⟨unaryW, unaryM, unaryQ, unaryT, _unaryS, _unaryH, _unaryC, unaryP, unaryN,
    _wmq, _mqt, _tsc, _cnp, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryM windowRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary unaryQ thresholdRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed thresholdUnary unaryT ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M windowRead ∧ Cont windowRead Q thresholdRead ∧
              Cont thresholdRead T ledgerRead ∧ Cont ledgerRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, thresholdRoute, ledgerRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.CauchyOscillationUp

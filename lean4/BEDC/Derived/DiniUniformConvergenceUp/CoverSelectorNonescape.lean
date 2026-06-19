import BEDC.Derived.DiniUniformConvergenceUp.NameCertObligations

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiniUniformConvergenceCoverSelectorNonescape [AskSetup] [PackageSetup]
    {K T F M W R E H C P N selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier K T F M W R E H C P N bundle pkg →
      Cont K T F →
        Cont F M W →
          Cont W R selectorRead →
            PkgSig bundle P pkg →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row T ∨ hsame row F ∨ hsame row M ∨
                        hsame row W ∨ hsame row R ∨ hsame row E ∨
                          hsame row selectorRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K T F ∧ Cont F M W ∧
                        Cont W R selectorRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory selectorRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier compactFinite familyWindow windowSelector provenancePkg localNamePkg
  have compactUnary : UnaryHistory K := carrier.left
  have finiteUnary : UnaryHistory T := carrier.right.left
  have modulusUnary : UnaryHistory M := carrier.right.right.right.left
  have readbackUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have familyUnary : UnaryHistory F :=
    unary_cont_closed compactUnary finiteUnary compactFinite
  have windowUnary : UnaryHistory W :=
    unary_cont_closed familyUnary modulusUnary familyWindow
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowUnary readbackUnary windowSelector
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row T ∨ hsame row F ∨ hsame row M ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row selectorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K T F ∧ Cont F M W ∧
              Cont W R selectorRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro selectorRead ⟨hsame_refl selectorRead, selectorUnary⟩
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
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, compactFinite, familyWindow, windowSelector,
            provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, selectorUnary⟩

end BEDC.Derived.DiniUniformConvergenceUp

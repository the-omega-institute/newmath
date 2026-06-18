import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiniUniformConvergenceCarrier [AskSetup] [PackageSetup]
    (compact finiteNet _family _modulus windows _readback sealRow _transportRow _replayRow provenance
      _localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compact ∧ UnaryHistory finiteNet ∧ UnaryHistory windows ∧
    UnaryHistory sealRow ∧ PkgSig bundle provenance pkg

theorem DiniUniformConvergenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compact finiteNet family modulus windows readback sealRow transportRow replayRow provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier compact finiteNet family modulus windows readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont compact finiteNet family ->
        Cont family windows readback ->
          Cont readback sealRow modulus ->
            PkgSig bundle localName pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨
                      hsame row modulus ∨ hsame row windows ∨ hsame row readback ∨
                        hsame row sealRow) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨
                      hsame row modulus ∨ hsame row windows ∨ hsame row readback ∨
                        hsame row sealRow ∨ hsame row localName)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧ UnaryHistory modulus := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier compactFiniteNet familyWindows readbackSeal localNamePkg
  obtain ⟨compactUnary, finiteNetUnary, windowsUnary, sealUnary, provenancePkg⟩ := carrier
  have familyUnary : UnaryHistory family :=
    unary_cont_closed compactUnary finiteNetUnary compactFiniteNet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed familyUnary windowsUnary familyWindows
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have sourceModulus :
      (fun row : BHist =>
        (hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨ hsame row modulus ∨
          hsame row windows ∨ hsame row readback ∨ hsame row sealRow) ∧ UnaryHistory row)
        modulus := by
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl modulus)))), modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨ hsame row modulus ∨
              hsame row windows ∨ hsame row readback ∨ hsame row sealRow) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compact ∨ hsame row finiteNet ∨ hsame row family ∨ hsame row modulus ∨
              hsame row windows ∨ hsame row readback ∨ hsame row sealRow ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro modulus sourceModulus
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
        cases sourceRow with
        | intro sourceRows _sourceUnary =>
            cases sourceRows with
            | inl compactRow =>
                exact Or.inl compactRow
            | inr rest₁ =>
                cases rest₁ with
                | inl finiteNetRow =>
                    exact Or.inr (Or.inl finiteNetRow)
                | inr rest₂ =>
                    cases rest₂ with
                    | inl familyRow =>
                        exact Or.inr (Or.inr (Or.inl familyRow))
                    | inr rest₃ =>
                        cases rest₃ with
                        | inl modulusRow =>
                            exact Or.inr (Or.inr (Or.inr (Or.inl modulusRow)))
                        | inr rest₄ =>
                            cases rest₄ with
                            | inl windowsRow =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl windowsRow))))
                            | inr rest₅ =>
                                cases rest₅ with
                                | inl readbackRow =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr (Or.inr (Or.inl readbackRow)))))
                                | inr sealRowSame =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr (Or.inr (Or.inl sealRowSame))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, modulusUnary⟩

theorem DiniUniformConvergenceCarrier_monotone_window [AskSetup] [PackageSetup]
    {compact finiteNet family modulus windows readback sealRow transportRow replayRow provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier compact finiteNet family modulus windows readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont compact finiteNet family ->
        Cont family windows readback ->
          UnaryHistory compact ∧ UnaryHistory finiteNet ∧ UnaryHistory family ∧
            UnaryHistory windows ∧ UnaryHistory readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier compactFiniteNet familyWindows
  obtain ⟨compactUnary, finiteNetUnary, windowsUnary, _sealUnary, provenancePkg⟩ := carrier
  have familyUnary : UnaryHistory family :=
    unary_cont_closed compactUnary finiteNetUnary compactFiniteNet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed familyUnary windowsUnary familyWindows
  exact ⟨compactUnary, finiteNetUnary, familyUnary, windowsUnary, readbackUnary, provenancePkg⟩

end BEDC.Derived.DiniUniformConvergenceUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.PackingNumberUp.TasteGate

namespace BEDC.Derived.PackingNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PackingNumberCarrier [AskSetup] [PackageSetup]
    (X eps U D B H C P N separatedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
    UnaryHistory B ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory separatedRead ∧ Cont X U separatedRead ∧
        PkgSig bundle P pkg

theorem PackingNumberCoveringDualHandoff [AskSetup] [PackageSetup]
    {X eps U D B H C P N separatedRead coveringRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackingNumberCarrier X eps U D B H C P N separatedRead bundle pkg →
      Cont separatedRead B coveringRead →
        PkgSig bundle coveringRead pkg →
          UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
            UnaryHistory B ∧ UnaryHistory separatedRead ∧ UnaryHistory coveringRead ∧
              Cont X U separatedRead ∧ Cont separatedRead B coveringRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle coveringRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier separatedCovering coveringPkg
  obtain ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, separatedUnary, sourceCentersSeparated, provenancePkg⟩ := carrier
  have coveringUnary : UnaryHistory coveringRead :=
    unary_cont_closed separatedUnary bUnary separatedCovering
  exact
      ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, separatedUnary, coveringUnary,
      sourceCentersSeparated, separatedCovering, provenancePkg, coveringPkg⟩

theorem PackingNumberCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X eps U D B H C P N separatedRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackingNumberCarrier X eps U D B H C P N separatedRead bundle pkg →
      Cont separatedRead D budgetRead →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨ hsame row B ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row budgetRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X U separatedRead ∧ Cont separatedRead D budgetRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier separatedBudget namePkg
  obtain ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, hUnary, cUnary, pUnary, nUnary,
    separatedUnary, sourceCentersSeparated, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed separatedUnary dUnary separatedBudget
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨ hsame row B ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X U separatedRead ∧ Cont separatedRead D budgetRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceCentersSeparated, separatedBudget, provenancePkg, namePkg⟩
  }
  have _carrierRows :
      UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
        UnaryHistory B ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
          UnaryHistory N :=
    ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, hUnary, cUnary, pUnary, nUnary⟩
  exact ⟨cert, budgetUnary⟩

theorem PackingNumberNamecertObligations [AskSetup] [PackageSetup]
    {X eps U D B H C P N separatedRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackingNumberCarrier X eps U D B H C P N separatedRead bundle pkg →
      Cont separatedRead D budgetRead →
        PkgSig bundle budgetRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨
                  hsame row B ∨ hsame row separatedRead ∨ hsame row budgetRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X U separatedRead ∧
                  Cont separatedRead D budgetRead ∧ PkgSig bundle budgetRead pkg)
              hsame ∧
            UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
              UnaryHistory B ∧ UnaryHistory separatedRead ∧ UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedBudget budgetPkg
  obtain ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, separatedUnary, sourceCentersSeparated, _provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed separatedUnary dUnary separatedBudget
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨
              hsame row B ∨ hsame row separatedRead ∨ hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X U separatedRead ∧ Cont separatedRead D budgetRead ∧
              PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceCentersSeparated, separatedBudget, budgetPkg⟩
  }
  exact
    ⟨cert, xUnary, epsUnary, uUnary, dUnary, bUnary, separatedUnary, budgetUnary⟩

end BEDC.Derived.PackingNumberUp

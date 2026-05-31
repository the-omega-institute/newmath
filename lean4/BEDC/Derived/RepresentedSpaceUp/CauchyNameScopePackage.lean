import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_cauchy_name_scope_package [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont schedule target cauchyRead →
        PkgSig bundle cauchyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
                  hsame row cauchyRead)
              (fun row : BHist =>
                hsame row cauchyRead ∧ PkgSig bundle cauchyRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory cauchyRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduleTargetRead cauchyReadPkg
  obtain ⟨_nameUnary, scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed scheduleUnary targetUnary scheduleTargetRead
  have sourceCauchyRead :
      (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row) cauchyRead := by
    exact ⟨hsame_refl cauchyRead, cauchyReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row cauchyRead)
          (fun row : BHist =>
            hsame row cauchyRead ∧ PkgSig bundle cauchyRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead sourceCauchyRead
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
      exact ⟨source.left, cauchyReadPkg, provenancePkg⟩
  }
  exact ⟨cert, cauchyReadUnary, provenancePkg⟩

end BEDC.Derived.RepresentedSpaceUp

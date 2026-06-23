import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationPublicExportReadiness [AskSetup] [PackageSetup]
    {W M Q T S H C P N frontierRead auditRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg →
      Cont W M frontierRead →
        Cont frontierRead Q auditRead →
          Cont auditRead S realRead →
            Cont realRead N publicRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                          hsame row S ∨ hsame row N ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W M frontierRead ∧
                          Cont frontierRead Q auditRead ∧ Cont auditRead S realRead ∧
                            Cont realRead N publicRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory frontierRead ∧ UnaryHistory auditRead ∧
                      UnaryHistory realRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierRoute auditRoute realRoute publicRoute provenancePkg namePkg
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, sUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _wm, _mq, _sc, _cn, _namePkg⟩ := carrier
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed wUnary mUnary frontierRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed frontierUnary qUnary auditRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed auditUnary sUnary realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row S ∨
              hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M frontierRead ∧ Cont frontierRead Q auditRead ∧
              Cont auditRead S realRead ∧ Cont realRead N publicRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, frontierRoute, auditRoute, realRoute, publicRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, frontierUnary, auditUnary, realUnary, publicUnary⟩

end BEDC.Derived.CauchyOscillationUp

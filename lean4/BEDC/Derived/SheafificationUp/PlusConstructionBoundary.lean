import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusConstructionBoundary [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverageRead localityRead gluingRead plusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont J P coverageRead →
        Cont L G localityRead →
          Cont localityRead S gluingRead →
            Cont gluingRead R plusRead →
              PkgSig bundle plusRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row plusRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row coverageRead ∨ hsame row plusRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont J P coverageRead ∧
                        Cont L G localityRead ∧ Cont localityRead S gluingRead ∧
                          Cont gluingRead R plusRead ∧ PkgSig bundle plusRead pkg)
                    hsame ∧
                  UnaryHistory coverageRead ∧ UnaryHistory plusRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverageRoute localityRoute gluingRoute plusRoute plusPkg
  obtain ⟨_cUnary, _tUnary, jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, rUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed jUnary pUnary coverageRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed lUnary gUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary sUnary gluingRoute
  have plusUnary : UnaryHistory plusRead :=
    unary_cont_closed gluingUnary rUnary plusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row plusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row Q ∨
                hsame row N ∨ hsame row coverageRead ∨ hsame row plusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J P coverageRead ∧ Cont L G localityRead ∧
              Cont localityRead S gluingRead ∧ Cont gluingRead R plusRead ∧
                PkgSig bundle plusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro plusRead ⟨hsame_refl plusRead, plusUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverageRoute, localityRoute, gluingRoute, plusRoute, plusPkg⟩
  }
  exact ⟨cert, coverageUnary, plusUnary⟩

end BEDC.Derived.SheafificationUp

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

theorem SheafificationLocalityScopeAddendum [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localityRead gluingRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localityRead →
        Cont localityRead G gluingRead →
          Cont gluingRead R scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                      hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                        hsame row R ∨ hsame row Q ∨ hsame row N ∨
                          hsame row localityRead ∨ hsame row gluingRead ∨
                            hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont P L localityRead ∧
                      Cont localityRead G gluingRead ∧ Cont gluingRead R scopedRead ∧
                        PkgSig bundle scopedRead pkg)
                  hsame ∧
                UnaryHistory localityRead ∧ UnaryHistory gluingRead ∧
                  UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier localityRoute gluingRoute scopedRoute scopedPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, _sUnary, _hUnary,
    rUnary, _qUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed gluingUnary rUnary scopedRoute
  have scopedSource :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead :=
    ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                hsame row R ∨ hsame row Q ∨ hsame row N ∨
                  hsame row localityRead ∨ hsame row gluingRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P L localityRead ∧
              Cont localityRead G gluingRead ∧ Cont gluingRead R scopedRead ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead scopedSource
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localityRoute, gluingRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, localityUnary, gluingUnary, scopedUnary⟩

end BEDC.Derived.SheafificationUp

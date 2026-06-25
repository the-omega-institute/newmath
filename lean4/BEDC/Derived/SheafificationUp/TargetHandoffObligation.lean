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

theorem SheafificationTargetHandoffObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localityRead gluingRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        Cont P L localityRead →
          Cont localityRead G gluingRead →
            Cont gluingRead S targetRead →
              PkgSig bundle targetRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row P ∨ hsame row L ∨
                        hsame row G ∨ hsame row S ∨ hsame row targetRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localityRead ∧
                        Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
                          PkgSig bundle targetRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory localityRead ∧
                    UnaryHistory gluingRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute localityRoute gluingRoute targetRoute targetPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _qPkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have gluingReadUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityReadUnary gUnary gluingRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingReadUnary sUnary targetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localityRead ∧
              Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
                PkgSig bundle targetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead
        ⟨hsame_refl targetRead, targetReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, localityRoute, gluingRoute, targetRoute, targetPkg⟩
  }
  exact ⟨cert, sourceReadUnary, localityReadUnary, gluingReadUnary, targetReadUnary⟩

end BEDC.Derived.SheafificationUp

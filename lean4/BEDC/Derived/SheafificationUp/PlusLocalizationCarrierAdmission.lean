import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusLocalizationCarrierAdmission [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N separatedRead coverLocalRead plusRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C J separatedRead →
        Cont P L coverLocalRead →
          Cont coverLocalRead G plusRead →
            Cont plusRead S handoffRead →
              PkgSig bundle handoffRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row separatedRead ∨ hsame row coverLocalRead ∨
                              hsame row plusRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C J separatedRead ∧
                        Cont P L coverLocalRead ∧ Cont coverLocalRead G plusRead ∧
                          Cont plusRead S handoffRead ∧
                            PkgSig bundle handoffRead pkg)
                    hsame ∧
                  UnaryHistory separatedRead ∧ UnaryHistory coverLocalRead ∧
                    UnaryHistory plusRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedRoute coverLocalRoute plusRoute handoffRoute handoffPkg
  obtain ⟨cUnary, _tUnary, jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, _namePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed cUnary jUnary separatedRoute
  have coverLocalUnary : UnaryHistory coverLocalRead :=
    unary_cont_closed pUnary lUnary coverLocalRoute
  have plusUnary : UnaryHistory plusRead :=
    unary_cont_closed coverLocalUnary gUnary plusRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed plusUnary sUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                hsame row R ∨ hsame row Q ∨ hsame row N ∨
                  hsame row separatedRead ∨ hsame row coverLocalRead ∨
                    hsame row plusRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C J separatedRead ∧ Cont P L coverLocalRead ∧
              Cont coverLocalRead G plusRead ∧ Cont plusRead S handoffRead ∧
                PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, separatedRoute, coverLocalRoute, plusRoute, handoffRoute,
          handoffPkg⟩
  }
  exact ⟨cert, separatedUnary, coverLocalUnary, plusUnary, handoffUnary⟩

end BEDC.Derived.SheafificationUp

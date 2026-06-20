import BEDC.Derived.BoundedBilinearMapUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedBilinearMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedBilinearMapCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {E F G B K L R T P N actionRead boundRead bilinearRead tensorRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory F →
        UnaryHistory G →
          UnaryHistory B →
            UnaryHistory K →
              UnaryHistory L →
                UnaryHistory R →
                  UnaryHistory T →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont E F actionRead →
                          Cont actionRead G boundRead →
                            Cont K R bilinearRead →
                              Cont bilinearRead T tensorRead →
                                Cont tensorRead N namedRead →
                                  PkgSig bundle P pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row E ∨ hsame row F ∨ hsame row G ∨
                                            hsame row B ∨ hsame row K ∨ hsame row L ∨
                                              hsame row R ∨ hsame row T ∨ hsame row P ∨
                                                hsame row N ∨ hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont E F actionRead ∧
                                            Cont actionRead G boundRead ∧
                                              Cont K R bilinearRead ∧
                                                Cont bilinearRead T tensorRead ∧
                                                  Cont tensorRead N namedRead ∧
                                                    PkgSig bundle P pkg)
                                        hsame ∧
                                      UnaryHistory actionRead ∧ UnaryHistory boundRead ∧
                                        UnaryHistory bilinearRead ∧
                                          UnaryHistory tensorRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig SemanticNameCert
  intro eUnary fUnary gUnary _bUnary kUnary _lUnary rUnary tUnary _pUnary nUnary
    actionRoute boundRoute bilinearRoute tensorRoute namedRoute provenancePkg
  have actionUnary : UnaryHistory actionRead := unary_cont_closed eUnary fUnary actionRoute
  have boundUnary : UnaryHistory boundRead := unary_cont_closed actionUnary gUnary boundRoute
  have bilinearUnary : UnaryHistory bilinearRead :=
    unary_cont_closed kUnary rUnary bilinearRoute
  have tensorUnary : UnaryHistory tensorRead :=
    unary_cont_closed bilinearUnary tUnary tensorRoute
  have namedUnary : UnaryHistory namedRead := unary_cont_closed tensorUnary nUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row B ∨ hsame row K ∨
              hsame row L ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E F actionRead ∧ Cont actionRead G boundRead ∧
              Cont K R bilinearRead ∧ Cont bilinearRead T tensorRead ∧
                Cont tensorRead N namedRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, actionRoute, boundRoute, bilinearRoute, tensorRoute, namedRoute,
          provenancePkg⟩
  }
  exact ⟨cert, actionUnary, boundUnary, bilinearUnary, tensorUnary, namedUnary⟩

end BEDC.Derived.BoundedBilinearMapUp

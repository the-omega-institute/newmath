import BEDC.Derived.WeakOmniscienceBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeakOmniscienceBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeakOmniscienceBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {R E K S Q F H C P N boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory E →
        UnaryHistory K →
          UnaryHistory S →
            UnaryHistory Q →
              UnaryHistory F →
                Cont R E boundaryRead →
                  PkgSig bundle P pkg →
                    (SemanticNameCert
                          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row R ∨ hsame row E ∨ hsame row K ∨ hsame row S ∨
                              hsame row Q ∨ hsame row F ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row boundaryRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont R E boundaryRead ∧
                              PkgSig bundle P pkg)
                          hsame) ∧
                      UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro rUnary eUnary _kUnary _sUnary _qUnary _fUnary boundaryRoute provenancePkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed rUnary eUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row E ∨ hsame row K ∨ hsame row S ∨ hsame row Q ∨
              hsame row F ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R E boundaryRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, provenancePkg⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.WeakOmniscienceBoundaryUp

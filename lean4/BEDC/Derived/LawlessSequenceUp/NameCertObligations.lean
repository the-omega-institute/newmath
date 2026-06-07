import BEDC.Derived.LawlessSequenceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LawlessSequenceNameCertObligations (x : LawlessSequenceUp) :
    ∃ W B I H C P N : BHist,
      x = LawlessSequenceUp.mk W B I H C P N ∧
        SemanticNameCert
          (fun row : BHist => hsame row N)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
          hsame ∧
          Cont BHist.Empty W W ∧ Cont BHist.Empty B B ∧ Cont BHist.Empty I I := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  cases x with
  | mk W B I H C P N =>
      let rowSurface := fun row : BHist =>
        hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
          hsame row P ∨ hsame row N
      have nameCert :
          SemanticNameCert (fun row : BHist => hsame row N) rowSurface rowSurface hsame := {
        core := {
          carrier_inhabited := Exists.intro N (hsame_refl N)
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
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source)))))
        ledger_sound := by
          intro _row source
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source)))))
      }
      exact
        ⟨W, B, I, H, C, P, N, rfl, nameCert, cont_left_unit W, cont_left_unit B,
          cont_left_unit I⟩

end BEDC.Derived.LawlessSequenceUp

namespace BEDC.Derived.LawlessSequenceUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceNameCertObligations [AskSetup] [PackageSetup]
    {W B I H C P N prefixRead digitRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory B →
        UnaryHistory I →
          UnaryHistory H →
            UnaryHistory C →
              UnaryHistory P →
                UnaryHistory N →
                  Cont I W prefixRead →
                    Cont prefixRead B digitRead →
                      Cont digitRead N namedRead →
                        hsame H (append C P) →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row W ∨ hsame row B ∨ hsame row I ∨
                                      hsame row prefixRead ∨ hsame row digitRead ∨
                                        hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont I W prefixRead ∧
                                      Cont prefixRead B digitRead ∧
                                        Cont digitRead N namedRead ∧
                                          hsame H (append C P) ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory prefixRead ∧ UnaryHistory digitRead ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro WUnary BUnary IUnary _HUnary _CUnary _PUnary NUnary indexWindowRead
    windowDigitRead digitNamedRead appendAnchor sourcePkg localPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed IUnary WUnary indexWindowRead
  have digitUnary : UnaryHistory digitRead :=
    unary_cont_closed prefixUnary BUnary windowDigitRead
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed digitUnary NUnary digitNamedRead
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                  (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, indexWindowRead, windowDigitRead, digitNamedRead,
            appendAnchor, sourcePkg, localPkg⟩
    }
  · exact ⟨prefixUnary, digitUnary, namedUnary⟩

end BEDC.Derived.LawlessSequenceUp.NameCertObligations

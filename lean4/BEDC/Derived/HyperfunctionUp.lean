import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperfunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperfunctionNamecertObligations [AskSetup] [PackageSetup]
    {T O B S Q A R D E K L M C P N boundaryRead sheafRead cohomologyRead complexRead
      distributionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory O →
        UnaryHistory B →
          UnaryHistory S →
            UnaryHistory Q →
              UnaryHistory A →
                UnaryHistory D →
                  UnaryHistory E →
                    Cont T O boundaryRead →
                      Cont boundaryRead S sheafRead →
                        Cont sheafRead Q cohomologyRead →
                          Cont cohomologyRead A complexRead →
                            Cont complexRead D distributionRead →
                              PkgSig bundle M pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row distributionRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row T ∨ hsame row O ∨ hsame row B ∨
                                          hsame row S ∨ hsame row Q ∨ hsame row A ∨
                                            hsame row R ∨ hsame row D ∨ hsame row E ∨
                                              hsame row K ∨ hsame row L ∨ hsame row M ∨
                                                hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                  hsame row distributionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont T O boundaryRead ∧
                                          Cont boundaryRead S sheafRead ∧
                                            Cont sheafRead Q cohomologyRead ∧
                                              Cont cohomologyRead A complexRead ∧
                                                Cont complexRead D distributionRead ∧
                                                  PkgSig bundle M pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory boundaryRead ∧ UnaryHistory sheafRead ∧
                                      UnaryHistory cohomologyRead ∧ UnaryHistory complexRead ∧
                                        UnaryHistory distributionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryT unaryO _unaryB unaryS unaryQ unaryA unaryD _unaryE boundaryRoute
    sheafRoute cohomologyRoute complexRoute distributionRoute packagePkg localNamePkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryT unaryO boundaryRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed boundaryUnary unaryS sheafRoute
  have cohomologyUnary : UnaryHistory cohomologyRead :=
    unary_cont_closed sheafUnary unaryQ cohomologyRoute
  have complexUnary : UnaryHistory complexRead :=
    unary_cont_closed cohomologyUnary unaryA complexRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed complexUnary unaryD distributionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row O ∨ hsame row B ∨ hsame row S ∨ hsame row Q ∨
              hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row K ∨
                hsame row L ∨ hsame row M ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row distributionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T O boundaryRead ∧ Cont boundaryRead S sheafRead ∧
              Cont sheafRead Q cohomologyRead ∧ Cont cohomologyRead A complexRead ∧
                Cont complexRead D distributionRead ∧ PkgSig bundle M pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro distributionRead ⟨hsame_refl distributionRead, distributionUnary⟩
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
                                  (Or.inr
                                    (Or.inr source.left))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, sheafRoute, cohomologyRoute, complexRoute,
          distributionRoute, packagePkg, localNamePkg⟩
  }
  exact
    ⟨cert, boundaryUnary, sheafUnary, cohomologyUnary, complexUnary, distributionUnary⟩

end BEDC.Derived.HyperfunctionUp

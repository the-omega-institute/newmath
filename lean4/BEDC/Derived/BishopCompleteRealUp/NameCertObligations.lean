import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompleteRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive BishopCompleteRealUp : Type where
  | mk (dyadic schedule regular real separated reflection transport replay provenance name :
      BHist) : BishopCompleteRealUp

def bishopCompleteRealFields : BishopCompleteRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompleteRealUp.mk D W R E S F H C P N => [D, W, R, E, S, F, H, C, P, N]

theorem BishopCompleteRealNamecertObligations [AskSetup] [PackageSetup]
    {D W R E S F H C P N scheduleRead regularRead realSeal separatedRead reflectionRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    bishopCompleteRealFields (BishopCompleteRealUp.mk D W R E S F H C P N) =
        [D, W, R, E, S, F, H, C, P, N] →
      UnaryHistory D →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory S →
                UnaryHistory F →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory N →
                        Cont D W scheduleRead →
                          Cont scheduleRead R regularRead →
                            Cont regularRead E realSeal →
                              Cont realSeal S separatedRead →
                                Cont separatedRead F reflectionRead →
                                  Cont reflectionRead C namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row D ∨ hsame row W ∨ hsame row R ∨
                                                hsame row E ∨ hsame row S ∨ hsame row F ∨
                                                  hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                    hsame row N ∨ hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont D W scheduleRead ∧
                                                Cont scheduleRead R regularRead ∧
                                                  Cont regularRead E realSeal ∧
                                                    Cont realSeal S separatedRead ∧
                                                      Cont separatedRead F reflectionRead ∧
                                                        Cont reflectionRead C namedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro fields dUnary wUnary rUnary eUnary sUnary fUnary _hUnary cUnary _nUnary scheduleRoute
    regularRoute realRoute separatedRoute reflectionRoute namedRoute pPkg nPkg
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed dUnary wUnary scheduleRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleUnary rUnary regularRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary eUnary realRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed realUnary sUnary separatedRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed separatedUnary fUnary reflectionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed reflectionUnary cUnary namedRoute
  have _acceptedFields :
      bishopCompleteRealFields (BishopCompleteRealUp.mk D W R E S F H C P N) =
        [D, W, R, E, S, F, H, C, P, N] := fields
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row S ∨
              hsame row F ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W scheduleRead ∧ Cont scheduleRead R regularRead ∧
              Cont regularRead E realSeal ∧ Cont realSeal S separatedRead ∧
                Cont separatedRead F reflectionRead ∧ Cont reflectionRead C namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, regularRoute, realRoute, separatedRoute, reflectionRoute,
          namedRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.BishopCompleteRealUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.SternBrocotUp.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SternBrocotRationalIntervalTreeConsumer [AskSetup] [PackageSetup]
    {A L U M F B Q R H C P N interval dyadic stream regseq realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A M Q →
      Cont Q interval dyadic →
        Cont dyadic stream regseq →
          Cont regseq realSeal N →
            UnaryHistory A →
              UnaryHistory M →
                UnaryHistory interval →
                  UnaryHistory stream →
                    UnaryHistory realSeal →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row N ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row A ∨ hsame row L ∨ hsame row U ∨
                                  hsame row M ∨ hsame row F ∨ hsame row B ∨
                                    hsame row Q ∨ hsame row R ∨ hsame row dyadic ∨
                                      hsame row stream ∨ hsame row regseq ∨
                                        hsame row realSeal ∨ hsame row N)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont A M Q ∧
                                  Cont Q interval dyadic ∧ Cont dyadic stream regseq ∧
                                    Cont regseq realSeal N ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory Q ∧ UnaryHistory dyadic ∧
                              UnaryHistory regseq ∧ UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro boundaryRoute dyadicRoute streamRoute sealRoute aUnary mUnary intervalUnary
    streamUnary realSealUnary _provenancePkg namePkg
  have qUnary : UnaryHistory Q :=
    unary_cont_closed aUnary mUnary boundaryRoute
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed qUnary intervalUnary dyadicRoute
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed dyadicUnary streamUnary streamRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed regseqUnary realSealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row L ∨ hsame row U ∨ hsame row M ∨
              hsame row F ∨ hsame row B ∨ hsame row Q ∨ hsame row R ∨
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A M Q ∧ Cont Q interval dyadic ∧
              Cont dyadic stream regseq ∧ Cont regseq realSeal N ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, dyadicRoute, streamRoute, sealRoute, namePkg⟩
  }
  exact ⟨cert, qUnary, dyadicUnary, regseqUnary, nUnary⟩

end BEDC.Derived.SternBrocotUp

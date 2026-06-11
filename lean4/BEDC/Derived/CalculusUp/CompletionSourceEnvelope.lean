import BEDC.Derived.CalculusUp.CompletionSourceEnvelopeObligations

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CalculusCompletionSourceEnvelope [AskSetup] [PackageSetup]
    (R L C D I Q Y H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame append PkgSig
  UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory C ∧ UnaryHistory D ∧
    UnaryHistory I ∧ UnaryHistory Q ∧ UnaryHistory Y ∧ hsame H (append T P) ∧
      PkgSig bundle P pkg

theorem CalculusCompletionSourceEnvelope_admission [AskSetup] [PackageSetup]
    {R L C D I Q Y H T P N derivativeRead integralRead limitRead dyadicRead realRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusCompletionSourceEnvelope R L C D I Q Y H T P N bundle pkg →
      UnaryHistory N →
        Cont C D derivativeRead →
          Cont C I integralRead →
            Cont C L limitRead →
              Cont Q Y dyadicRead →
                Cont dyadicRead R realRead →
                  Cont realRead N publicRead →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨
                              hsame row Q ∨ hsame row Y ∨ hsame row R ∨
                                hsame row H ∨ hsame row publicRead)
                          (fun row : BHist =>
                            CalculusCompletionSourceEnvelope R L C D I Q Y H T P N
                              bundle pkg ∧
                              UnaryHistory row ∧ Cont C D derivativeRead ∧
                                Cont C I integralRead ∧ Cont C L limitRead ∧
                                  Cont Q Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                                    Cont realRead N publicRead ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                          UnaryHistory limitRead ∧ UnaryHistory dyadicRead ∧
                            UnaryHistory realRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro envelope nUnary derivativeRoute integralRoute limitRoute dyadicRoute realRoute
    publicRoute publicPkg
  rcases envelope with
  ⟨rUnary, lUnary, cUnary, dUnary, iUnary, qUnary, yUnary, hTransport,
    provenancePkg⟩
  have baseCert :=
    CalculusCompletionSourceEnvelopeObligations
      (R := R) (L := L) (C := C) (D := D) (I := I) (Q := Q) (Y := Y) (N := N)
      (P := P) (derivativeRead := derivativeRead) (integralRead := integralRead)
      (limitRead := limitRead) (dyadicRead := dyadicRead) (realRead := realRead)
      (publicRead := publicRead) (bundle := bundle) (pkg := pkg)
      rUnary lUnary cUnary dUnary iUnary qUnary yUnary nUnary derivativeRoute
      integralRoute limitRoute dyadicRoute realRoute publicRoute provenancePkg publicPkg
  rcases baseCert with
  ⟨_cert, derivativeUnary, integralUnary, limitUnary, dyadicUnary, realUnary, publicUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨⟨rUnary, lUnary, cUnary, dUnary, iUnary, qUnary, yUnary, hTransport,
              provenancePkg⟩,
            source.right, derivativeRoute, integralRoute, limitRoute, dyadicRoute,
            realRoute, publicRoute, publicPkg⟩
    }
  · exact
      ⟨derivativeUnary, integralUnary, limitUnary, dyadicUnary, realUnary, publicUnary⟩

end BEDC.Derived.CalculusUp

import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_schedule_factorization [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory E →
        UnaryHistory T →
          UnaryHistory S →
            PkgSig bundle P pkg →
              PkgSig bundle N pkg →
                Cont M E I →
                  Cont I T tailRead →
                    Cont tailRead S sealRead →
                      PkgSig bundle sealRead pkg →
                        SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row E ∨ hsame row I ∨
                              hsame row T ∨ hsame row S ∨ hsame row R ∨
                                hsame row H ∨ hsame row C0 ∨ hsame row P ∨
                                  hsame row N ∨ hsame row tailRead ∨
                                    hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M E I ∧ Cont I T tailRead ∧
                              Cont tailRead S sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle sealRead pkg)
                          hsame ∧
                          UnaryHistory I ∧ UnaryHistory tailRead ∧
                            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro mUnary eUnary tUnary sUnary pPkg _nPkg indexRoute tailRoute sealRoute sealPkg
  have indexUnary : UnaryHistory I :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
            hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
              hsame row P ∨ hsame row N ∨ hsame row tailRead ∨
                hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M E I ∧ Cont I T tailRead ∧
            Cont tailRead S sealRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle sealRead pkg)
        hsame := by
    refine
      { core :=
          { carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealUnary⟩
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows sourceRow
      exact
        ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
          unary_transport sourceRow.right sameRows⟩
    · intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr sourceRow.left))))))))))
    · intro _row sourceRow
      exact ⟨sourceRow.right, indexRoute, tailRoute, sealRoute, pPkg, sealPkg⟩
  exact ⟨cert, indexUnary, tailUnary, sealUnary⟩

end BEDC.Derived.CanonicalTailChoiceUp

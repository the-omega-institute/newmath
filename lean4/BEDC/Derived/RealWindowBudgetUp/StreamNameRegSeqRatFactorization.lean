import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_streamname_regseqrat_factorization [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow streamRead dyadicRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont request windows streamRead →
        Cont streamRead dyadic dyadicRead →
          Cont dyadicRead handoff regseqRead →
            Cont regseqRead realSeal realRead →
              PkgSig bundle streamRead pkg →
                PkgSig bundle dyadicRead pkg →
                  PkgSig bundle regseqRead pkg →
                    PkgSig bundle realRead pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                              disclosure transport route provenance nameRow bundle pkg ∧
                            (hsame row streamRead ∨ hsame row dyadicRead ∨
                              hsame row regseqRead ∨ hsame row realRead))
                        (fun row : BHist =>
                          Cont request windows streamRead ∧
                            Cont streamRead dyadic dyadicRead ∧
                              Cont dyadicRead handoff regseqRead ∧
                                Cont regseqRead realSeal realRead ∧
                                  (hsame row streamRead ∨ hsame row dyadicRead ∨
                                    hsame row regseqRead ∨ hsame row realRead))
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont PkgSig
  intro carrier requestWindowsStream streamDyadicRead dyadicHandoffRegseq
    regseqRealSealRead streamPkg dyadicPkg regseqPkg realPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed carrier.request_unary carrier.windows_unary requestWindowsStream
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary carrier.dyadic_unary streamDyadicRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicReadUnary carrier.handoff_unary dyadicHandoffRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary carrier.realSeal_unary regseqRealSealRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro streamRead ⟨carrier, Or.inl (hsame_refl streamRead)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowStream =>
            exact Or.inl (hsame_trans (hsame_symm same) rowStream)
        | inr tail =>
            cases tail with
            | inl rowDyadic =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic))
            | inr tail' =>
                cases tail' with
                | inl rowRegseq =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowRegseq)))
                | inr rowReal =>
                    exact Or.inr (Or.inr (Or.inr (hsame_trans (hsame_symm same) rowReal)))
    }
    pattern_sound := by
      intro row source
      exact
        ⟨requestWindowsStream, streamDyadicRead, dyadicHandoffRegseq, regseqRealSealRead,
          source.right⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl rowStream =>
          cases rowStream
          exact ⟨streamUnary, carrier.provenance_pkg⟩
      | inr tail =>
          cases tail with
          | inl rowDyadic =>
              cases rowDyadic
              exact ⟨dyadicReadUnary, carrier.provenance_pkg⟩
          | inr tail' =>
              cases tail' with
              | inl rowRegseq =>
                  cases rowRegseq
                  exact ⟨regseqReadUnary, carrier.provenance_pkg⟩
              | inr rowReal =>
                  cases rowReal
                  exact ⟨realReadUnary, carrier.provenance_pkg⟩
  }

end BEDC.Derived.RealWindowBudgetUp

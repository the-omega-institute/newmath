import BEDC.Derived.DedekindMacNeilleCompletionUp.NameCertObligations

namespace BEDC.Derived.DedekindMacNeilleCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DedekindMacNeilleCompletionRealSealNonescape [AskSetup] [PackageSetup]
    {L U K Q E H C P N realSeal namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L U K →
      Cont K Q E →
        Cont E C realSeal →
          Cont realSeal N namedRead →
            UnaryHistory L →
              UnaryHistory U →
                UnaryHistory Q →
                  UnaryHistory C →
                    UnaryHistory N →
                      PkgSig bundle namedRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row L ∨ hsame row U ∨ hsame row K ∨
                                hsame row Q ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row realSeal ∨ hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont L U K ∧ Cont K Q E ∧
                                Cont E C realSeal ∧ Cont realSeal N namedRead ∧
                                  PkgSig bundle namedRead pkg)
                            hsame ∧
                          UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory realSeal ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro routeLU routeKQ routeEC routeNamed unaryL unaryU unaryQ unaryC unaryN namedPkg
  have unaryK : UnaryHistory K := unary_cont_closed unaryL unaryU routeLU
  have unaryE : UnaryHistory E := unary_cont_closed unaryK unaryQ routeKQ
  have realSealUnary : UnaryHistory realSeal := unary_cont_closed unaryE unaryC routeEC
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realSealUnary unaryN routeNamed
  have namedSource :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row K ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row realSeal ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U K ∧ Cont K Q E ∧ Cont E C realSeal ∧
              Cont realSeal N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead namedSource
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLU, routeKQ, routeEC, routeNamed, namedPkg⟩
  }
  exact ⟨cert, unaryK, unaryE, realSealUnary, namedUnary⟩

end BEDC.Derived.DedekindMacNeilleCompletionUp

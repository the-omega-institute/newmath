import BEDC.Derived.CompactIntervalFixedPointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactIntervalFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointNameCertObligations [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N intervalRead mapRead bisectionRead windowRead rationalRead
      sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J → UnaryHistory G → UnaryHistory R → UnaryHistory B → UnaryHistory W →
      UnaryHistory Q → UnaryHistory E → UnaryHistory H → UnaryHistory C →
        PkgSig bundle P pkg →
          Cont J G intervalRead →
            Cont intervalRead R mapRead →
              Cont mapRead B bisectionRead →
                Cont bisectionRead W windowRead →
                  Cont windowRead Q rationalRead →
                    Cont rationalRead E sealRead →
                      Cont H C localRead →
                        PkgSig bundle localRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
                                  hsame row W ∨ hsame row Q ∨ hsame row E ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row sealRead ∨
                                        hsame row localRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont J G intervalRead ∧
                                  Cont intervalRead R mapRead ∧ Cont mapRead B bisectionRead ∧
                                    Cont bisectionRead W windowRead ∧
                                      Cont windowRead Q rationalRead ∧
                                        Cont rationalRead E sealRead ∧
                                          Cont H C localRead ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle localRead pkg)
                              hsame ∧
                            UnaryHistory intervalRead ∧ UnaryHistory mapRead ∧
                              UnaryHistory bisectionRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory rationalRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary hUnary cUnary pkgP
    jg intervalR mapB bisectionW windowQ rationalE hc pkgLocal
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed jUnary gUnary jg
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed intervalUnary rUnary intervalR
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed mapUnary bUnary mapB
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary bisectionW
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowUnary qUnary windowQ
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary eUnary rationalE
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead ∨
                  hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J G intervalRead ∧ Cont intervalRead R mapRead ∧
              Cont mapRead B bisectionRead ∧ Cont bisectionRead W windowRead ∧
                Cont windowRead Q rationalRead ∧ Cont rationalRead E sealRead ∧
                  Cont H C localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, jg, intervalR, mapB, bisectionW, windowQ, rationalE,
          hc, pkgP, pkgLocal⟩
  }
  exact
    ⟨cert, intervalUnary, mapUnary, bisectionUnary, windowUnary, rationalUnary,
      sealUnary, localUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp

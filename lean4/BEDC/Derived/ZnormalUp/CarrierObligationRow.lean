import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalCarrierObligationRow [AskSetup] [PackageSetup]
    {T F V K R H C P N carrierRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory V →
          UnaryHistory K →
            UnaryHistory R →
              UnaryHistory H →
                UnaryHistory C →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      Cont T F carrierRead →
                        Cont carrierRead V K →
                          Cont H C finalRead →
                            SemanticNameCert
                                (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row V ∨
                                    hsame row K ∨ hsame row R ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row carrierRead ∨ hsame row finalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory carrierRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryT unaryF unaryV _unaryK _unaryR unaryH unaryC pkgP pkgN
    contTFCarrier contCarrierVK contHCFinal
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed unaryT unaryF contTFCarrier
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed unaryH unaryC contHCFinal
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact ⟨finalRead, hsame_refl finalRead, finalReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _row' leftSame rightSame
          exact hsame_trans leftSame rightSame
        carrier_respects_equiv := by
          intro row row' same source
          constructor
          · exact hsame_trans (hsame_symm same) source.left
          · exact unary_transport source.right same
      }
      pattern_sound := by
        intro row source
        exact Or.inr
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
        intro row source
        exact ⟨source.right, pkgP, pkgN⟩
    }
  · exact ⟨carrierReadUnary, finalReadUnary⟩

end BEDC.Derived.ZnormalUp

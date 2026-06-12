import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceLinearCauchySeal [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L cauchyRead completionRead toleranceRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg ∧ PkgSig bundle L pkg) →
      Cont M Q cauchyRead →
        Cont cauchyRead S completionRead →
          Cont completionRead R toleranceRead →
            Cont toleranceRead E sealRead →
              Cont sealRead L namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
                          hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row Z ∨
                            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M Q cauchyRead ∧
                          Cont cauchyRead S completionRead ∧
                            Cont completionRead R toleranceRead ∧
                              Cont toleranceRead E sealRead ∧ Cont sealRead L namedRead ∧
                                PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory BanachSpaceUp
  intro carrierRows cauchyRoute completionRoute toleranceRoute sealRoute namedRoute namedPkg
  obtain ⟨_VUnary, _NUnary, MUnary, QUnary, SUnary, RUnary, EUnary, _ZUnary,
    _HUnary, _CUnary, _PUnary, LUnary, _provenancePkg, _localPkg⟩ := carrierRows
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed MUnary QUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary SUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary RUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary EUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary LUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q cauchyRead ∧ Cont cauchyRead S completionRead ∧
              Cont completionRead R toleranceRead ∧ Cont toleranceRead E sealRead ∧
                Cont sealRead L namedRead ∧ PkgSig bundle namedRead pkg)
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
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cauchyRoute, completionRoute, toleranceRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.BanachSpaceUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySumLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySumLimitNamecertObligations [AskSetup] [PackageSetup]
    {X Y S Q D A H C P N leftRead rightRead sumRead toleranceRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory Y →
        UnaryHistory S →
          UnaryHistory Q →
            UnaryHistory D →
              UnaryHistory A →
                UnaryHistory N →
                  Cont X S leftRead →
                    Cont Y S rightRead →
                      Cont leftRead rightRead sumRead →
                        Cont sumRead D toleranceRead →
                          Cont toleranceRead A sealRead →
                            Cont sealRead N namedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row Y ∨ hsame row S ∨
                                          hsame row Q ∨ hsame row D ∨ hsame row A ∨
                                            hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont X S leftRead ∧
                                          Cont Y S rightRead ∧
                                            Cont leftRead rightRead sumRead ∧
                                              Cont sumRead D toleranceRead ∧
                                                Cont toleranceRead A sealRead ∧
                                                  Cont sealRead N namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle namedRead pkg)
                                      hsame ∧
                                    UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                                      UnaryHistory sumRead ∧ UnaryHistory toleranceRead ∧
                                        UnaryHistory sealRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro xUnary yUnary _sUnary _qUnary dUnary aUnary nUnary leftCont rightCont sumCont
    toleranceCont sealCont nameCont provenancePkg namedPkg
  have _transportRow : BHist := H
  have _replayRow : BHist := C
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed xUnary _sUnary leftCont
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed yUnary _sUnary rightCont
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed leftUnary rightUnary sumCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sumUnary dUnary toleranceCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary aUnary sealCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary nameCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row Q ∨ hsame row D ∨
              hsame row A ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S leftRead ∧ Cont Y S rightRead ∧
              Cont leftRead rightRead sumRead ∧ Cont sumRead D toleranceRead ∧
                Cont toleranceRead A sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftCont, rightCont, sumCont, toleranceCont, sealCont, nameCont,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, sumUnary, toleranceUnary, sealUnary, namedUnary⟩

end BEDC.Derived.CauchySumLimitUp
